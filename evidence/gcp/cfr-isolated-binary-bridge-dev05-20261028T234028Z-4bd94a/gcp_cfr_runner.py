"""Remote-only CFR Lean runner; invoke on the established GCP builder.

Retains immutable inputs and all stage outputs, including failed attempts.
The caller must hold the task-owned campaign lock for the full invocation.
"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tarfile
import time


def approved_axiom_profile(value):
    """Validate printed standard axioms, allowing their single universe parameter.

    Lean's dependency report prints abstract named universe parameters here,
    not arbitrary level expressions. Conservatively accept one lowercase
    parameter (optionally with a numeric index) or a numeral. This excludes
    reserved words and compound expressions; preserve raw spelling in receipts.
    """
    raw = [part.strip() for part in value.split(',')]
    if not value.strip():
        return [], []
    normalized = []
    for token in raw:
        match = re.fullmatch(r'(propext|Classical\.choice|Quot\.sound)(?:\.\{([a-z](?:_[0-9]+)?|[0-9]+)\})?', token)
        if not match or (match.group(1) == 'propext' and match.group(2) is not None):
            raise ValueError('Unapproved or malformed axiom token: '+repr(token))
        normalized.append(match.group(1))
    if len(normalized) != len(set(normalized)):
        raise ValueError('Duplicate axiom declaration in one profile')
    return raw, normalized


def digest(path):
    with path.open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def write(path, data):
    path.write_text(json.dumps(data, indent=2)+'\n', encoding='utf-8')


def now():
    return datetime.now(timezone.utc).isoformat()


def owned_warning_headers(text):
    """Recognize both Lean and Lake warning orders, excluding package paths."""
    owned = r'(?:CorruptedFieldRecovery(?:/[^:\s]+\.lean|\.lean)|checks/[^:\s]+\.lean)'
    prefix = r'(?:\./)*'
    patterns = [re.compile(r'^warning:\s+'+prefix+owned+r':'),
                re.compile(r'^'+prefix+owned+r':\d+:\d+:\s*warning:')]
    found = []
    for line in text.splitlines():
        plain = re.sub(r'\x1b\[[0-9;]*m', '', line)
        if any(pattern.search(plain) for pattern in patterns):
            found.append(line)
    return found


def extract(archive, destination):
    with tarfile.open(archive) as source:
        for item in source.getmembers():
            target = (destination/item.name).resolve()
            if not target.is_relative_to(destination.resolve()):
                raise RuntimeError('Unsafe archive path')
        source.extractall(destination, filter='data')


def main():
    if sys.platform != 'linux' or not os.environ.get('CFR_GCP_RUN'):
        raise RuntimeError('Remote-only runner: Linux and explicit cloud run identity required')
    run = Path(sys.argv[1]).resolve()
    campaign = Path(sys.argv[2]).resolve()
    manifest = json.loads((run/'capture-manifest.json').read_text())
    assert manifest['run'] == run.name == os.environ['CFR_GCP_RUN']
    assert manifest['compile_host'] == 'GCP'
    assert manifest['utf8_no_bom_verified']
    assert manifest['lean_toolchain'] == 'leanprover/lean4:v4.30.0'
    assert digest(run/'inputs.tar.gz') == manifest['archive_sha256']
    logs = run/'logs'
    logs.mkdir(exist_ok=True)
    stages = []
    receipt = dict(run=manifest['run'], compile_host='GCP', project=manifest['project'],
                   instance=manifest['instance'], zone=manifest['zone'], started_utc=now(),
                   status='running', stage_outcomes=stages,
                   source_sha256=manifest['source_sha256'], dependencies=manifest['dependencies'],
                   authoritative_scope='Exact captured sources and requested targets only; not full manuscript certification')
    write(run/'terminal-receipt.json', receipt)

    def stage(name, command, cwd, timeout=1800):
        print('STAGE='+name, flush=True)
        (run/'current-stage').write_text(name+'\n')
        start = time.monotonic()
        with (logs/(name+'.stdout.txt')).open('wb') as stdout, (logs/(name+'.stderr.txt')).open('wb') as stderr:
            process = subprocess.Popen(command, cwd=cwd, stdout=stdout, stderr=stderr, start_new_session=True)
            timed_out = False
            try:
                code = process.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    process.wait(timeout=15)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                code = 124
        entry = dict(stage=name, command=command, exit_code=code, timed_out=timed_out,
                     elapsed_seconds=round(time.monotonic()-start, 3))
        stages.append(entry)
        write(run/'terminal-receipt.json', receipt)
        if code:
            raise RuntimeError('Stage failed: '+name+' exit='+str(code))

    def identities(source, packages):
        expected_owned = {name for name in manifest['source_sha256']
                          if name.startswith('CorruptedFieldRecovery/') and name.endswith('.lean')}
        actual_owned = {p.relative_to(source).as_posix()
                        for p in (source/'CorruptedFieldRecovery').rglob('*.lean')}
        assert actual_owned == expected_owned, 'Unexpected or missing owned Lean sources: '+repr(actual_owned ^ expected_owned)
        for name, expected in manifest['source_sha256'].items():
            assert digest(source/name) == expected, name
        for package in manifest['dependencies']:
            path = packages/package['name']
            actual = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
            assert actual == package['rev'], package['name']
            subprocess.run(['git', '-C', str(path), 'diff', '--exit-code', 'HEAD', '--'], check=True)

    try:
        campaign.mkdir(exist_ok=True)
        source = campaign/'source'
        packages = campaign/'packages'
        ltar = campaign/'mathlib-cache'
        previous = campaign/'last-success.json'
        receipt['cache_predecessor'] = json.loads(previous.read_text()) if previous.exists() else None
        if not packages.exists():
            assets = json.loads((run/'bootstrap-assets.json').read_text())
            for name, sha in assets.items():
                assert digest(run/name) == sha, name
            packages.mkdir()
            extract(run/'space-pinned-dependencies.tar.gz', packages)
            for path in packages.iterdir():
                if path.is_dir():
                    subprocess.run(['git', '-C', str(path), 'read-tree', 'HEAD'], check=True)
                    # The transport archive came from Windows. Materialize exact
                    # committed blobs in our private copy, preserving the archive
                    # and leaving every historical/shared checkout untouched.
                    subprocess.run(['git', '-C', str(path), 'config', 'core.autocrlf', 'false'], check=True)
                    subprocess.run(['git', '-C', str(path), 'checkout-index', '--all', '--force'], check=True)
            ltar.mkdir(exist_ok=True)
            extract(run/'space-mathlib-cache.tar', ltar)
        source.mkdir(exist_ok=True)
        extracted = run/'immutable-source'
        extracted.mkdir()
        extract(run/'inputs.tar.gz', extracted)
        for name, expected in manifest['source_sha256'].items():
            assert digest(extracted/name) == expected, name
            destination = source/name
            destination.parent.mkdir(parents=True, exist_ok=True)
            if not destination.exists() or digest(destination) != expected:
                shutil.copyfile(extracted/name, destination)
        (source/'.lake').mkdir(exist_ok=True)
        link = source/'.lake/packages'
        if not link.exists():
            link.symlink_to(packages, target_is_directory=True)
        assert link.resolve() == packages.resolve()
        tool = Path(manifest['builder_profile']['toolchain_bin']) if manifest.get('builder_profile') else Path.home()/'quantyra-space-tools/lean-4.30.0-linux/bin'
        assert (tool/'lean').is_file() and (tool/'lake').is_file()
        os.environ['PATH'] = str(tool)+os.pathsep+os.environ['PATH']
        os.environ['MATHLIB_NO_CACHE_ON_UPDATE'] = '1'
        os.environ['MATHLIB_CACHE_DIR'] = str(ltar)
        receipt['toolchain_binary_sha256'] = {name:digest(tool/name) for name in ['lean', 'lake']}
        identities(source, packages)
        receipt['source_and_dependencies_verified_before'] = True
        receipt['dependency_tree_sha1'] = {
            p['name']:subprocess.check_output(['git', '-C', str(packages/p['name']),
                         'rev-parse', 'HEAD^{tree}'], text=True).strip()
            for p in manifest['dependencies']}
        stage('lean-version', ['lean', '--version'], source, 60)
        stage('lake-version', ['lake', '--version'], source, 60)
        lean_version = (logs/'lean-version.stdout.txt').read_text()
        assert '4.30.0' in lean_version
        reported = re.search(r'commit\s+([0-9a-f]{7,40})', lean_version)
        expected_commit = 'd024af099ca4bf2c86f649261ebf59565dc8c622'
        assert reported and expected_commit.startswith(reported.group(1)), lean_version
        receipt['lean_commit_verified'] = expected_commit
        receipt['reported_lean_commit'] = reported.group(1)
        imports = set()
        for name in manifest['source_sha256']:
            if name.endswith('.lean'):
                text = (source/name).read_text(encoding='utf-8')
                imports.update(re.findall(r'^import\s+(Mathlib\.[A-Za-z0-9_.]+)', text, re.M))
        for item in imports:
            assert (packages/'mathlib'/Path(*item.split('.'))).with_suffix('.lean').is_file(), item
        # Public pinned mathlib artifacts, unpacked/built only inside this campaign.
        if not (campaign/'dependency-cache-ready').exists():
            stage('dependency-cache', ['lake', 'exe', 'cache', 'get', *sorted(imports)], source)
            (campaign/'dependency-cache-ready').write_text(now()+'\n')
        else:
            # New imports may require additional public artifacts; get is incremental.
            stage('dependency-cache-incremental', ['lake', 'exe', 'cache', 'get', *sorted(imports)], source)
        stage('build', ['lake', 'build', *manifest['targets']], source)
        if manifest['audit']:
            stage('audit', ['lake', 'env', 'lean', manifest.get('audit_path', 'checks/Audit.lean')], source)
        identities(source, packages)
        receipt['source_and_dependencies_verified_after'] = True
        texts = {p.name:p.read_text(encoding='utf-8', errors='replace') for p in logs.glob('*.txt')}
        combined = '\n'.join(texts.values())
        assert not re.search(r'error:|unsolved goals|sorryAx', combined)
        warnings = owned_warning_headers(combined)
        frozen = campaign/'warning-baseline.json'
        if not frozen.exists():
            write(frozen, dict(source_sha256=manifest['source_sha256'], dependencies=manifest['dependencies'],
                               warnings=warnings, baseline_run=manifest['run']))
        receipt['owned_warning_headers'] = warnings
        receipt['frozen_warning_baseline'] = json.loads(frozen.read_text())
        assert set(warnings) <= set(receipt['frozen_warning_baseline']['warnings']), 'New owned warning headers'
        if manifest['audit']:
            text = texts.get('audit.stdout.txt', '')+'\n'+texts.get('audit.stderr.txt', '')
            reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)
            empty = re.findall(r"'([^']+)' does not depend on any axioms", text)
            audit_file = source/manifest.get('audit_path', 'checks/Audit.lean')
            expected = re.findall(r'^#print axioms\s+(\S+)\s*$', audit_file.read_text(), re.M)
            names = [name for name,_ in reports]+empty
            assert len(names) == len(set(names)) and set(names) == set(expected)
            profiles = {name:approved_axiom_profile(values) for name,values in reports}
            axioms = sorted({a for _,normalized in profiles.values() for a in normalized})
            receipt['reported_axiom_profiles_raw'] = {name:raw for name,(raw,_) in profiles.items()}
            receipt['audited_declarations'] = sorted(names)
            receipt['reported_axioms'] = axioms
            receipt['type_axiom_audit'] = dict(source_sha256=digest(audit_file),
                stdout_sha256=digest(logs/'audit.stdout.txt'), stderr_sha256=digest(logs/'audit.stderr.txt'),
                semantic_acceptance='Not inferred; Root must inspect emitted types against the manuscript target.')
            blocks = {}
            for name in manifest.get('audited_exports', []):
                begin, end = 'CFR_TYPE_BEGIN:'+name+'\n', 'CFR_TYPE_END:'+name+'\n'
                assert text.count(begin) == text.count(end) == 1, name
                body = text.split(begin, 1)[1].split(end, 1)[0]
                blocks[name] = dict(emitted_type=body, sha256=hashlib.sha256(body.encode('utf-8')).hexdigest())
            if blocks:
                write(logs/'emitted-types.json', blocks)
                receipt['type_axiom_audit']['emitted_types_sha256'] = digest(logs/'emitted-types.json')
                receipt['type_axiom_audit']['type_block_sha256'] = {n:b['sha256'] for n,b in blocks.items()}
        receipt['status'] = 'passed'
        write(previous, dict(run=manifest['run'], source_sha256=manifest['source_sha256'],
                             dependencies=manifest['dependencies'], targets=manifest['targets'], utc=now()))
        return 0
    except Exception as exc:
        receipt['status'] = 'failed'
        receipt['failure'] = repr(exc)
        raise
    finally:
        receipt['finished_utc'] = now()
        # Runner tee streams remain open until this process and its shell exit.
        # Hash only closed stage logs here; collection hashes every raw log.
        receipt['log_sha256'] = {p.relative_to(run).as_posix():digest(p) for p in sorted(logs.glob('*.txt'))
                                 if not p.name.startswith('runner.')}
        write(run/'terminal-receipt.json', receipt)


if __name__ == '__main__':
    raise SystemExit(main())
