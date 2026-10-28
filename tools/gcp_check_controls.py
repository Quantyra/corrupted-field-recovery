"""Pure-Python cloud-control checks; invokes no Lean, Lake or cloud command."""
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import runpy
import tarfile
import uuid

ROOT = Path(__file__).resolve().parents[1]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    runner = ROOT/'tools/gcp_cfr_runner.py'
    controller = ROOT/'tools/gcp_cfr.py'
    for path in [runner, controller, Path(__file__)]:
        ast.parse(path.read_text(encoding='utf-8'))
    classify = runpy.run_path(str(runner))['owned_warning_headers']
    owned = [
        'warning: CorruptedFieldRecovery/BinaryTensor.lean:12:3: unused h',
        'CorruptedFieldRecovery/Bridge.lean:4:2: warning: unused x',
        'warning: checks/CaptureAudit.lean:2:0: example',
        'checks/Audit.lean:9:1: warning: example',
        'warning: ././CorruptedFieldRecovery.lean:1:0: root',
        './checks/Audit.lean:9:1: warning: example',
    ]
    dependency = [
        'warning: .lake/packages/mathlib/Mathlib/Foo.lean:1:0: inherited',
        './.lake/packages/test/CorruptedFieldRecovery/Foo.lean:3:0: warning: inherited',
        'warning: ./.lake/packages/test/checks/Foo.lean:3:0: inherited',
    ]
    assert classify('\n'.join(owned+dependency)) == owned
    members, captures, generated_audits = 0, [], []
    for path in sorted((ROOT/'evidence/gcp').glob('*/capture-manifest.json')):
        data = json.loads(path.read_text())
        archive = path.parent/'inputs.tar.gz'
        assert sha(archive.read_bytes()) == data['archive_sha256']
        with tarfile.open(archive) as tar:
            assert set(tar.getnames()) == set(data['source_sha256'])
            for name, expected in data['source_sha256'].items():
                content = tar.extractfile(name).read()
                assert sha(content) == expected, name
                content.decode('utf-8', errors='strict')
                assert not content.startswith(b'\xef\xbb\xbf')
                members += 1
            if data.get('audited_exports'):
                audit = tar.extractfile(data['audit_path']).read().decode('utf-8')
                for setting in ['pp.universes', 'pp.explicit', 'pp.fullNames']:
                    assert 'set_option '+setting+' true' in audit
                assert 'set_option pp.proofs false' not in audit
                for name in data['audited_exports']:
                    assert '#check @'+name+'\n' in audit
                    assert '#print axioms '+name+'\n' in audit
                generated_audits.append(data['run'])
        captures.append(data['run'])
    target_path = ROOT/'formal/target-specification.json'
    target = json.loads(target_path.read_text())
    for name in ['manuscript', 'post_archive_resource_clarification']:
        record = target['frozen_sources'][name]
        assert sha((ROOT/record['path']).read_bytes()) == record['sha256'], name
    assert len(target['required_conclusions']) == 11
    assert target['complete_certification'] is False
    assert all(r['accepted_type_fingerprint'] is None for r in target['required_conclusions'])
    receipt = dict(status='passed', compile_invoked=False, cloud_invoked=False,
        command='python -B tools/gcp_check_controls.py',
        warning_fixture_cases=len(owned)+len(dependency), captures_verified=captures,
        source_members_verified=members, explicit_type_audits_verified=generated_audits,
        target_source_hashes_verified=True, required_conclusion_groups=11,
        source_sha256={p.relative_to(ROOT).as_posix():sha(p.read_bytes())
                       for p in [controller, runner, Path(__file__), target_path]})
    run = 'cfr-control-check-'+datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'-'+uuid.uuid4().hex[:6]
    out = ROOT/'evidence/gcp'/run
    out.mkdir()
    with (out/'receipt.json').open('x', encoding='utf-8', newline='\n') as file:
        json.dump(receipt, file, indent=2)
        file.write('\n')
    print(json.dumps(dict(run=run, **receipt), indent=2))


if __name__ == '__main__':
    main()
