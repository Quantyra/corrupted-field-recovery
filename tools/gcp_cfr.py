"""Isolated CFR cloud control and immutable captures; never execute local Lean.

Use the repository's Python interpreter to run this controller. It invokes only
the established gcloud route and never reads the historical Space state file.
"""
import argparse
import base64
from datetime import datetime, timezone
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import uuid

if hasattr(sys.stdout, 'reconfigure'):
    sys.stdout.reconfigure(encoding='utf-8', errors='backslashreplace')
    sys.stderr.reconfigure(encoding='utf-8', errors='backslashreplace')

ROOT = Path(__file__).resolve().parents[1]
CONTROLLER_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
EVIDENCE = ROOT / 'evidence' / 'gcp'
SDK = Path('C:/Users/dfred/AppData/Local/Google/Cloud SDK/google-cloud-sdk')
CLOUD = [str(SDK/'platform/bundledpython/python.exe'), '-S', str(SDK/'lib/gcloud.py')]
PROJECT = 'quantyra-lean-cert-20260915'
ZONE = 'us-central1-a'
VM = 'quantyra-lean-builder-01'
ACCOUNT = 'dfredriksen@quantyra.org'
PROFILE = json.loads((ROOT/'tools/gcp-builder-profile.json').read_text(encoding='utf-8'))
PROJECT, VM, ZONE, ACCOUNT = (PROFILE[k] for k in ['project', 'instance', 'zone', 'account'])
FLAGS = ['--project='+PROJECT, '--zone='+ZONE, '--account='+ACCOUNT, '--quiet']
CAMPAIGN = PROFILE['campaign']
ASSETS = Path('C:/Users/dfred/QuantyraTools/SpaceProofs')


def utc():
    return datetime.now(timezone.utc).isoformat()


def unique(label):
    return 'cfr-'+label+'-'+datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'-'+uuid.uuid4().hex[:6]


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x', encoding='utf-8', newline='\n') as f:
        json.dump(value, f, indent=2)
        f.write('\n')


def cloud(args, out, label, flags=True):
    out.mkdir(parents=True, exist_ok=True)
    args = list(args)
    if args[:2] in [['compute', 'ssh'], ['compute', 'scp']] and PROFILE.get('ssh_host_key_fingerprint'):
        kind = '--ssh-flag=' if args[1] == 'ssh' else '--scp-flag='
        args += [kind+'-hostkey', kind+PROFILE['ssh_host_key_fingerprint']]
    result = subprocess.run(CLOUD+args+(FLAGS if flags else []), capture_output=True)
    (out/(label+'.stdout.txt')).write_bytes(result.stdout)
    (out/(label+'.stderr.txt')).write_bytes(result.stderr)
    save(out/(label+'.exit.json'), dict(exit_code=result.returncode, utc=utc(),
         command=['gcloud']+args+(FLAGS if flags else [])))
    print(label, 'exit', result.returncode, flush=True)
    if result.stdout:
        display = result.stdout.decode('utf-8', errors='replace')
        try:
            structured = json.loads(display)
            if isinstance(structured, dict) and structured.get('kind') == 'compute#instance':
                display = json.dumps({k:structured.get(k) for k in ['name', 'id', 'status', 'machineType']})
        except ValueError:
            pass
        print(display[-7000:], flush=True)
    if result.returncode:
        print(result.stderr.decode('utf-8', errors='replace')[-4000:], flush=True)
        raise RuntimeError('Cloud operation failed; preserve evidence and do not duplicate a launch: '+label)
    return result.stdout


def ssh(script, out, label):
    encoded = base64.b64encode(script.encode('utf-8')).decode('ascii')
    return cloud(['compute', 'ssh', VM, '--tunnel-through-iap',
                  '--command=echo '+encoded+' | base64 -d | bash'], out, label)


def run_directory(name):
    if not re.fullmatch(r'cfr-[a-zA-Z0-9_-]+', name):
        raise ValueError('Invalid run name')
    out = EVIDENCE/name
    if not (out/'capture-manifest.json').is_file():
        raise ValueError('Missing immutable capture')
    manifest = json.loads((out/'capture-manifest.json').read_text())
    if (manifest['project'], manifest['instance'], manifest['zone']) != (PROJECT, VM, ZONE):
        raise ValueError('Capture belongs to another builder; preserve it and create a fresh capture for this profile')
    return out


def submission_guard(run):
    """One prelaunch SSH, in dependency order; never start a compiler here."""
    if not re.fullmatch(r'cfr-[A-Za-z0-9_-]+', run):
        raise ValueError('Unsafe run identity')
    return ('set -eu\nif pgrep -x lean || pgrep -x lake; then exit 73; fi\n'
        'test -x "'+PROFILE['toolchain_bin']+'/lean"\n'
        'mkdir -p "$HOME/quantyra-cfr-runs/'+CAMPAIGN+'"\n'
        'flock -n "$HOME/quantyra-cfr-runs/'+CAMPAIGN+'/lock" true\n'
        'run="$HOME/quantyra-cfr-runs/'+run+'"\n'
        'test ! -e "$run"\nmkdir "$run"\n'
        'printf "CFR_HOME=%s\\n" "$HOME"\n'
        'if test -d "$HOME/quantyra-cfr-runs/'+CAMPAIGN+'/packages/mathlib/.git"; '
        'then echo CFR_CACHE=READY; else echo CFR_CACHE=MISSING; fi\n')


def submit(args):
    out = run_directory(args.run)
    manifest = json.loads((out/'capture-manifest.json').read_text())
    if (out/'launch-request.json').exists():
        raise RuntimeError('Launch already requested: observe this handle; never duplicate it')
    if not manifest['utf8_no_bom_verified']:
        raise RuntimeError('Encoding preflight failed')
    assert hashlib.sha256((out/'inputs.tar.gz').read_bytes()).hexdigest() == manifest['archive_sha256']
    runner = ROOT/'tools/gcp_cfr_runner.py'
    runner_bytes = runner.read_bytes()
    (out/'gcp_cfr_runner.py').write_bytes(runner_bytes)
    assets = {name:hashlib.file_digest((ASSETS/name).open('rb'), 'sha256').hexdigest()
              for name in ['space-pinned-dependencies.tar.gz', 'space-mathlib-cache.tar']}
    save(out/'bootstrap-assets.json', assets)
    state = json.loads(cloud(['compute', 'instances', 'describe', VM, '--format=json'], out, 'submission-instance-state'))
    ownership = dict(initial_state=state['status'], started_for_task=False,
                     project=PROJECT, instance=VM, zone=ZONE, run=args.run, utc=utc())
    if state['status'] == 'TERMINATED':
        save(out/'instance-start-intent.json', dict(initial_state='TERMINATED', run=args.run, utc=utc(),
             note='If transport fails, observe actual VM state; do not repeat the start blindly.'))
        cloud(['compute', 'instances', 'start', VM], out, 'start-task-instance')
        ownership['started_for_task'] = True
    elif state['status'] != 'RUNNING':
        raise RuntimeError('Instance not ready: '+state['status'])
    save(out/'instance-ownership.json', ownership)
    prepare_execution(out, args.run, runner_bytes)
    preflight = ssh(submission_guard(args.run), out, 'submission-preflight')
    remote = '$HOME/quantyra-cfr-runs/'+args.run
    home = next(line.removeprefix('CFR_HOME=') for line in preflight.decode().splitlines() if line.startswith('CFR_HOME='))
    remote_scp = scp_destination(home, args.run)
    cloud(['compute', 'scp', str(out/'inputs.tar.gz'), str(out/'capture-manifest.json'),
           str(out/'gcp_cfr_runner.py'), str(out/'run.sh'), str(out/'bootstrap-assets.json'),
           remote_scp, '--tunnel-through-iap'], out, 'upload-capture-and-controller')
    # Task-owned copies only; neither source archives nor other campaign caches are mutated.
    have_packages = next(line.removeprefix('CFR_CACHE=') for line in preflight.decode().splitlines() if line.startswith('CFR_CACHE=')).encode()
    transfer = ['inputs.tar.gz', 'capture-manifest.json', 'gcp_cfr_runner.py', 'run.sh', 'bootstrap-assets.json']
    if have_packages.decode().strip() != 'READY':
        cloud(['compute', 'scp', *[str(ASSETS/name) for name in assets], remote_scp,
               '--tunnel-through-iap'], out, 'upload-bootstrap-assets')
        transfer += list(assets)
    hashes = {n:hashlib.sha256((out/n if (out/n).exists() else ASSETS/n).read_bytes()).hexdigest() for n in transfer}
    checks = '\n'.join(sha+'  '+n for n,sha in hashes.items())
    ssh('set -eu\ncd "'+remote+'"\nsha256sum -c <<\'CFR_HASHES\'\n'+checks+'\nCFR_HASHES\n', out, 'verify-transferred-inputs')
    save(out/'launch-request.json', dict(utc=utc(), run=args.run, campaign=CAMPAIGN,
         note='An observation/transport timeout must not trigger another launch.'))
    ssh('set -eu\nrun="'+remote+'"\n'
        'nohup bash "$run/run.sh" > "$run/launch.log" 2>&1 < /dev/null &\n'
        'echo "$!" > "$run/runner-pid"\nprintf "REMOTE_PID="; cat "$run/runner-pid"\n', out, 'launch-once')


def prepare_execution(out, run, runner_bytes):
    script = '''#!/usr/bin/env bash
set -euo pipefail
run="$HOME/quantyra-cfr-runs/RUN"
campaign="$HOME/quantyra-cfr-runs/CAMPAIGN"
mkdir -p "$run/logs"
exec > >(tee "$run/logs/runner.stdout.txt") 2> >(tee "$run/logs/runner.stderr.txt" >&2)
trap 'code=$?; echo "$code" > "$run/exit-code"; date -u +%FT%TZ > "$run/finished-utc"' EXIT
date -u +%FT%TZ > "$run/started-utc"
exec 9> "$campaign/lock"
flock -n 9 || exit 75
echo 'RUNNERHASH  '"$run/gcp_cfr_runner.py" | sha256sum -c -
CFR_GCP_RUN=RUN python3 "$run/gcp_cfr_runner.py" "$run" "$campaign"
'''.replace('RUNNERHASH', hashlib.sha256(runner_bytes).hexdigest()).replace('CAMPAIGN', CAMPAIGN).replace(
        'quantyra-cfr-runs/RUN', 'quantyra-cfr-runs/'+run).replace('CFR_GCP_RUN=RUN ', 'CFR_GCP_RUN='+run+' ')
    (out/'run.sh').write_text(script, encoding='utf-8', newline='\n')
    save(out/'execution-manifest.json', dict(runner_sha256=hashlib.sha256(runner_bytes).hexdigest(),
         shell_sha256=hashlib.sha256((out/'run.sh').read_bytes()).hexdigest(), campaign=CAMPAIGN,
         controller_sha256=CONTROLLER_SHA256,
         stage_timeout_seconds=1800, ownership_policy='Stop task-started VM only after outcomes retained and no other work.'))


def scp_destination(home, run):
    """PuTTY SCP requires an absolute remote path; do not rely on tilde expansion."""
    if not re.fullmatch(r'/[A-Za-z0-9_./-]+', home) or '..' in home.split('/'):
        raise ValueError('Unsafe remote HOME')
    if not re.fullmatch(r'cfr-[A-Za-z0-9_-]+', run):
        raise ValueError('Unsafe run identity')
    return VM+':'+home.rstrip('/')+'/quantyra-cfr-runs/'+run+'/'


def resume_prelaunch(args):
    """Continue a preserved failed upload, never recreate inputs or launch twice."""
    out = run_directory(args.run)
    if (out/'launch-request.json').exists():
        raise RuntimeError('Launch requested already; observe the existing handle')
    manifest = json.loads((out/'capture-manifest.json').read_text())
    assert hashlib.sha256((out/'inputs.tar.gz').read_bytes()).hexdigest() == manifest['archive_sha256']
    if not (out/'execution-manifest.json').exists():
        prepare_execution(out, args.run, (out/'gcp_cfr_runner.py').read_bytes())
    label = unique('resume-prelaunch')
    remote = '$HOME/quantyra-cfr-runs/'+args.run
    preflight = ssh('set -eu\nrun="'+remote+'"\n'
        'test -d "$run"\ntest ! -e "$run/runner-pid"\ntest ! -e "$run/started-utc"\n'
        'if pgrep -x lean || pgrep -x lake; then exit 73; fi\n'
        'flock -n "$HOME/quantyra-cfr-runs/'+CAMPAIGN+'/lock" true\n'
        'printf "CFR_HOME=%s\\n" "$HOME"\n', out, label+'-guard')
    home = next(line.removeprefix('CFR_HOME=') for line in preflight.decode().splitlines() if line.startswith('CFR_HOME='))
    destination = scp_destination(home, args.run)
    names = ['inputs.tar.gz', 'capture-manifest.json', 'gcp_cfr_runner.py', 'run.sh', 'bootstrap-assets.json']
    assets = json.loads((out/'bootstrap-assets.json').read_text())
    cloud(['compute', 'scp', *[str(out/n) for n in names], destination, '--tunnel-through-iap'], out, label+'-upload')
    ready = ssh('test ! -d "$HOME/quantyra-cfr-runs/'+CAMPAIGN+'/packages/mathlib/.git" || echo READY\n', out, label+'-cache')
    if ready.decode().strip() != 'READY':
        cloud(['compute', 'scp', *[str(ASSETS/n) for n in assets], destination, '--tunnel-through-iap'], out, label+'-assets')
        names += list(assets)
    expected = {n:hashlib.sha256((out/n if (out/n).exists() else ASSETS/n).read_bytes()).hexdigest() for n in names}
    checks = '\n'.join(sha+'  '+n for n,sha in expected.items())
    ssh('set -eu\ncd "'+remote+'"\nsha256sum -c <<\'CFR_HASHES\'\n'+checks+'\nCFR_HASHES\n', out, label+'-verify')
    save(out/(label+'-verified-transfer.json'), dict(remote_home=home, sha256=expected, utc=utc()))
    save(out/'launch-request.json', dict(utc=utc(), run=args.run, campaign=CAMPAIGN, resumed_prelaunch=True))
    ssh('set -eu\nrun="'+remote+'"\n'
        'test ! -e "$run/runner-pid"\ntest ! -e "$run/started-utc"\n'
        'nohup bash "$run/run.sh" > "$run/launch.log" 2>&1 < /dev/null &\n'
        'echo "$!" > "$run/runner-pid"\nprintf "REMOTE_PID="; cat "$run/runner-pid"\n', out, 'launch-once')


def observation(args):
    out = run_directory(args.run)
    label = unique(args.mode)
    remote = '$HOME/quantyra-cfr-runs/'+args.run
    if args.mode == 'observe':
        ssh('run="'+remote+'"\n'
            'if test -f "$run/exit-code"; then printf "TERMINAL_EXIT="; cat "$run/exit-code"; fi\n'
            'cat "$run/current-stage" 2>/dev/null || true\n'
            'cat "$run/terminal-receipt.json" 2>/dev/null || true\n'
            'tail -n 30 "$run/logs/build.stdout.txt" 2>/dev/null || true\n'
            'tail -n 30 "$run/logs/build.stderr.txt" 2>/dev/null || true\n', out, label)
    elif args.mode == 'collect':
        packaged = ssh('set -eu\nrun="'+remote+'"\n'
            'test -f "$run/exit-code"\ncd "$run"\n'
            'tar -czf collected-evidence.tar.gz logs exit-code started-utc finished-utc launch.log runner-pid '
            '$(test ! -e terminal-receipt.json || echo terminal-receipt.json)\n'
            'sha256sum collected-evidence.tar.gz\nprintf "CFR_HOME=%s\\n" "$HOME"\n', out, label+'-package')
        archive = out/(label+'-evidence.tar.gz')
        home = next(line.removeprefix('CFR_HOME=') for line in packaged.decode().splitlines() if line.startswith('CFR_HOME='))
        cloud(['compute', 'scp', scp_destination(home, args.run)+'collected-evidence.tar.gz',
               str(archive), '--tunnel-through-iap'], out, label+'-download')
        with tarfile.open(archive) as tar:
            for member in tar.getmembers():
                if member.isfile():
                    dest = out/'collected'/member.name
                    if not dest.resolve().is_relative_to((out/'collected').resolve()):
                        raise RuntimeError('Unsafe evidence path')
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    data = tar.extractfile(member).read()
                    if dest.exists() and dest.read_bytes() != data:
                        raise RuntimeError('Terminal evidence changed: '+member.name)
                    dest.write_bytes(data)
        collected = out/'collected'
        receipt = collected/'terminal-receipt.json'
        if receipt.exists():
            for name, expected in json.loads(receipt.read_text()).get('log_sha256', {}).items():
                actual = hashlib.sha256((collected/name).read_bytes()).hexdigest()
                if actual != expected:
                    raise RuntimeError('Collected stage-log hash mismatch: '+name)
        save(out/(label+'-collection.json'), dict(run=args.run, utc=utc(),
             archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),
             retained_sha256={p.relative_to(collected).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in collected.rglob('*') if p.is_file()}))
        print('COLLECTED', args.run)


def stop_owned(args):
    out = run_directory(args.run)
    authority = (EVIDENCE/args.ownership_receipt).resolve() if args.ownership_receipt else out/'instance-ownership.json'
    if not authority.is_relative_to(EVIDENCE.resolve()):
        raise ValueError('Ownership receipt must be retained campaign evidence')
    ownership = json.loads(authority.read_text())
    created = ownership.get('created_for_task') is True
    owned_run = ownership.get('run') == args.run or (created and ownership.get('run') == 'isolated-builder-profile')
    expected_state = 'ABSENT' if created else 'TERMINATED'
    if not owned_run or ownership.get('initial_state') != expected_state or ownership.get('started_for_task') is not True:
        raise RuntimeError('This task did not start the instance; no stop authority from this handle')
    if args.ownership_receipt:
        assert all(ownership.get(k) == v for k,v in [('project',PROJECT),('instance',VM),('zone',ZONE)]) if created else True
        assert (authority.parent/('create-intent.json' if created else 'start-intent.json')).is_file()
        result = json.loads((authority.parent/('create-isolated-instance.exit.json' if created else 'start-task-instance.exit.json')).read_text())
        assert result['exit_code'] == 0
        assert ['compute', 'instances', 'create' if created else 'start', VM] == result['command'][1:5]
    live = [p.parent for p in EVIDENCE.glob('*/launch-request.json')]
    for directory in live:
        if not (directory/'collected/exit-code').is_file():
            raise RuntimeError('A launched CFR outcome is not collected: '+directory.name)
    label = unique('shutdown')
    remote = '$HOME/quantyra-cfr-runs/'+CAMPAIGN
    raw = ssh('set -eu\n'
        'if pgrep -x lean || pgrep -x lake; then exit 73; fi\n'
        'campaign="'+remote+'"\nflock -n "$campaign/lock" true\n'
        'if test -f "$campaign/last-success.json"; then cat "$campaign/last-success.json"; '
        'else echo NO_SUCCESSFUL_CACHE_CHECKPOINT; fi\n'
        'printf "TASK_CACHE_RETAINED\\n"\n'
        'if test -d "$campaign/source/.lake/build"; then '
        'find "$campaign/source/.lake/build" -type f -name "*.olean" -print0 | sort -z | xargs -0 -r sha256sum; '
        'else echo NO_BUILD_OUTPUTS; fi\n',
        out, label+'-preservation-preflight')
    save(out/(label+'-preservation.json'), dict(campaign=CAMPAIGN, utc=utc(),
         output_sha256=hashlib.sha256(raw).hexdigest(), all_task_outcomes_collected=True,
         no_active_lean_or_lake=True, task_lock_free=True, persistent_cache_retained=True))
    current = json.loads(cloud(['compute', 'instances', 'describe', VM, '--format=json'], out, label+'-initial-state'))
    if created:
        original = json.loads((authority.parent/'create-isolated-instance.stdout.txt').read_text(encoding='utf-8'))
        if not isinstance(original, list) or len(original) != 1 or current.get('id') != original[0].get('id'):
            raise RuntimeError('Instance identity differs from task creation receipt; refusing shutdown')
    state = current['status']
    if state != 'RUNNING':
        raise RuntimeError('Expected running task-owned instance, got '+state)
    if PROFILE.get('ephemeral_external_ip'):
        cloud(['compute', 'instances', 'delete-access-config', VM,
               '--network-interface=nic0', '--access-config-name=external-nat'], out, label+'-remove-task-egress')
    cloud(['compute', 'instances', 'stop', VM], out, label+'-stop-task-instance')
    final = cloud(['compute', 'instances', 'describe', VM, '--format=value(status)'], out, label+'-final-state').decode().strip()
    if final != 'TERMINATED':
        raise RuntimeError('Shutdown not confirmed: '+final)
    save(out/(label+'-result.json'), dict(initial_state=state, final_state=final, utc=utc(),
         started_for_task=True, stop_verified=True, persistent_cache_retained=True))


def audit_source(targets, exports):
    imports = sorted(set(['CorruptedFieldRecovery']+targets))
    audit = '\n'.join('import '+name for name in imports)+(
        '\n\nset_option pp.universes true\nset_option pp.explicit false\n'
        'set_option pp.fullNames true\nset_option pp.piBinderTypes true\n'
        'set_option pp.piBinderNames true\nset_option pp.piBinderNames.hygienic true\n'
        'set_option pp.proofs true\nset_option pp.deepTerms true\n'
        'set_option pp.maxSteps 1000000\nset_option maxRecDepth 10000\n')
    for name in exports:
        audit += '\n#eval IO.println "CFR_TYPE_BEGIN:'+name+'"\n#check @'+name+'\n'
        audit += '#eval IO.println "CFR_TYPE_END:'+name+'"\n#print axioms '+name+'\n'
    return audit.encode('utf-8')


def expected_type_tokens(exports):
    known = {
        'CorruptedFieldRecovery.balanced_first_three_preserves_axes':
            ['K', 'c', 'hc', 'T', 'h0', 'h1', 'h2', 'fieldContraction0', 'fieldContraction1', 'fieldContraction2', 'And'],
        'CorruptedFieldRecovery.balanced_first_three_block_form': ['K', 'c', 'hc', 'T', 'h0', 'h1', 'h2', 'fieldBlock0', 'fieldBlock1', 'fieldBlock2'],
        'CorruptedFieldRecovery.linearMap_scalar_of_commutes_generator': ['F', 'K', 'A', 'hgen', 'hcomm', 'Eq', 'HMul.hMul', 'A 1'],
    }
    return {name:known[name] for name in exports if name in known}


def capture(args):
    run = unique(args.label)
    out = EVIDENCE/run
    out.mkdir(parents=True)
    commit = subprocess.check_output(['git', 'rev-parse', args.commit or 'HEAD'], cwd=ROOT, text=True).strip()
    if args.commit:
        names = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', commit], cwd=ROOT, text=True).splitlines()
        names = [n for n in names if n.startswith('CorruptedFieldRecovery/') and n.endswith('.lean')
                 or n in {'CorruptedFieldRecovery.lean', 'checks/Audit.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'}]
        files = {n: subprocess.check_output(['git', 'show', commit+':'+n], cwd=ROOT) for n in names}
    else:
        names = [p.relative_to(ROOT).as_posix() for p in (ROOT/'CorruptedFieldRecovery').rglob('*.lean')]
        names += ['CorruptedFieldRecovery.lean', 'checks/Audit.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain']
        files = {n:(ROOT/n).read_bytes() for n in names}
    audit_path = 'checks/Audit.lean'
    if args.audit_export:
        for name in args.audit_export:
            if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.\']*', name):
                raise ValueError('Invalid audited declaration name')
        audit_path = 'checks/CaptureAudit.lean'
        files[audit_path] = audit_source(args.target or [], args.audit_export)
    errors = []
    for name, content in files.items():
        if content.startswith(b'\xef\xbb\xbf'):
            errors.append(name+': UTF-8 BOM')
        try:
            decoded = content.decode('utf-8', errors='strict')
            if name.endswith('.lean') and any(bad in decoded for bad in ['\ufffd', '\u00e2\u2020', '\u00c3\u00a2']):
                errors.append(name+': suspected mathematical glyph corruption')
        except UnicodeDecodeError:
            errors.append(name+': invalid UTF-8')
    with tarfile.open(out/'inputs.tar.gz', 'w:gz') as archive:
        for name, content in sorted(files.items()):
            info = tarfile.TarInfo(name)
            info.mode = 0o644
            info.size = len(content)
            archive.addfile(info, io.BytesIO(content))
    manifest = dict(run=run, utc=utc(), parent_commit=commit,
                    source_kind='git-commit' if args.commit else 'working-tree-offer',
                    project=PROJECT, instance=VM, zone=ZONE, compile_host='GCP',
                    builder_profile=PROFILE,
                    targets=args.target or ['CorruptedFieldRecovery'], audit=not args.no_audit,
                    audit_path=audit_path, audited_exports=args.audit_export or [],
                    expected_type_tokens=expected_type_tokens(args.audit_export or []),
                    source_sha256={n:hashlib.sha256(b).hexdigest() for n,b in sorted(files.items())},
                    dependencies=json.loads(files['lake-manifest.json'])['packages'],
                    lean_toolchain=files['lean-toolchain'].decode('utf-8').strip(),
                    archive_sha256=hashlib.sha256((out/'inputs.tar.gz').read_bytes()).hexdigest(),
                    utf8_no_bom_verified=not errors, encoding_errors=errors)
    save(out/'capture-manifest.json', manifest)
    print(json.dumps({k:manifest[k] for k in ['run', 'source_kind', 'targets', 'audit',
                     'audit_path', 'archive_sha256', 'source_sha256', 'utf8_no_bom_verified', 'encoding_errors']}, indent=2))
    if errors:
        raise RuntimeError('Captured offered bytes, but encoding preflight failed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='mode', required=True)
    sub.add_parser('preflight')
    cap = sub.add_parser('capture')
    cap.add_argument('--label', default='baseline')
    cap.add_argument('--commit')
    cap.add_argument('--target', action='append')
    cap.add_argument('--no-audit', action='store_true')
    cap.add_argument('--audit-export', action='append')
    remote = sub.add_parser('inspect')
    remote.add_argument('--run')
    for mode in ['submit', 'resume-prelaunch', 'observe', 'collect', 'stop-owned']:
        handle = sub.add_parser(mode)
        handle.add_argument('--run', required=True)
        if mode == 'stop-owned':
            handle.add_argument('--ownership-receipt', help='Relative evidence/gcp path to a separate task reacquisition receipt')
    args = parser.parse_args()
    if args.mode == 'capture':
        capture(args)
    elif args.mode == 'submit':
        submit(args)
    elif args.mode == 'resume-prelaunch':
        resume_prelaunch(args)
    elif args.mode in ['observe', 'collect']:
        observation(args)
    elif args.mode == 'stop-owned':
        stop_owned(args)
    elif args.mode == 'preflight':
        out = EVIDENCE/unique('preflight')
        cloud(['auth', 'list', '--format=json'], out, 'authenticated-account', flags=False)
        raw = cloud(['compute', 'instances', 'describe', VM, '--format=json'], out, 'instance-state')
        data = json.loads(raw)
        save(out/'ownership-observation.json', dict(utc=utc(), initial_state=data['status'],
             started_for_task=False, project=PROJECT, instance=VM, zone=ZONE,
             policy='Stop only a task-started instance after preserving outcomes and excluding other ownership.'))
    else:
        out = EVIDENCE/unique('inspect')
        script = '''set -eu
hostname
python3 --version
printf 'ACTIVE_LEAN_AND_LAKE\n'
pgrep -a -x lean || true
pgrep -a -x lake || true
df -h "$HOME" /dev/shm
printf 'EXISTING_TOOLCHAIN\n'
test -f /var/lib/quantyra-cfr-builder-ready
printf 'CFR_WORKSPACE\n'
ls -ld "$HOME/quantyra-cfr-runs" 2>/dev/null || true
printf 'PINNED_ARCHIVES\n'
find /tmp -maxdepth 1 -type f \\( -name 'space-pinned-dependencies.tar.gz' -o -name 'space-mathlib-cache.tar' \\) -printf '%f %s\\n'
'''
        ssh(script, out, 'remote-preflight')


if __name__ == '__main__':
    main()
