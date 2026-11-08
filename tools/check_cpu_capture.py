"""Exercise immutable CPU packet custody and fail-closed routing; no Lean or SSH."""
import argparse
import contextlib
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
from unittest.mock import patch

import gcp_cfr as controller


def main():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        originals = {
            'CorruptedFieldRecovery/Fixture.lean': b'-- untracked fixture bytes\n',
            'CorruptedFieldRecovery.lean': b'import CorruptedFieldRecovery.Fixture\n',
            'checks/Audit.lean': b'-- original audit remains in capture\n',
            'lakefile.toml': b'name = "fixture"\n',
            'lake-manifest.json': b'{"packages": []}\n',
            'lean-toolchain': b'leanprover/lean4:v4.30.0\n',
            'tools/cpu_cfr_runner.py': b'# Non-executable CPU control fixture\n',
            'tools/gcp_cfr_runner.py': b'# Non-executable shared control fixture\n',
            'tools/cpu_cfr.py': b'# Non-executable transport fixture\n',
        }
        for name, data in originals.items():
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)

        def args(host='cpu-02', **overrides):
            values = dict(label='fixture', commit=None, compile_host=host,
                          no_audit=False, target=['CorruptedFieldRecovery.Fixture'],
                          audit_export=['CorruptedFieldRecovery.fixture'])
            values.update(overrides)
            return argparse.Namespace(**values)

        with patch.object(controller, 'ROOT', root), \
             patch.object(controller, 'EVIDENCE', root/'evidence/gcp'), \
             patch.object(controller, 'unique', return_value='cfr-fixture'), \
             patch.object(controller.subprocess, 'check_output', return_value='a'*40) as git:
            with contextlib.redirect_stdout(io.StringIO()):
                controller.capture(args())
            out = root/'evidence/cpu/cfr-fixture'
            manifest = json.loads((out/'capture-manifest.json').read_text())
            assert manifest['compile_host'] == 'CPU'
            assert hashlib.sha256((out/'capture-controller.py').read_bytes()).hexdigest() == manifest['capture_controller_sha256']
            for name, expected in manifest['execution_control_sha256'].items():
                assert hashlib.sha256((out/name).read_bytes()).hexdigest() == expected
                assert (out/name).read_bytes() == originals['tools/'+name]
            assert manifest['instance'] == 'cpu-02'
            assert manifest['project'] is manifest['zone'] is manifest['builder_profile'] is None
            assert manifest['prospective_compiler'] == {
                'host': 'cpu-02', 'admission': 'NOT_ESTABLISHED',
                'runtime_adapter': 'IMPLEMENTED_NOT_QUALIFIED', 'execution': 'NOT_SUBMITTED'}
            assert hashlib.sha256((out/'inputs.tar.gz').read_bytes()).hexdigest() == manifest['archive_sha256']
            with tarfile.open(out/'inputs.tar.gz') as archive:
                assert set(archive.getnames()) == set(manifest['source_sha256'])
                for name, expected in manifest['source_sha256'].items():
                    data = archive.extractfile(name).read()
                    assert hashlib.sha256(data).hexdigest() == expected
                    if name in originals:
                        assert data == originals[name] == (root/name).read_bytes()
            assert not (out/'terminal-receipt.json').exists()
            assert git.call_count == 1 and git.call_args.args[0] == ['git', 'rev-parse', 'HEAD']

            # Invalid or unaudited CPU offers must fail before creating another packet.
            for invalid in [args('unknown'), args(no_audit=True), args(audit_export=[]), args(target=[])]:
                try:
                    controller.capture(invalid)
                except ValueError:
                    pass
                else:
                    raise AssertionError('Accepted invalid CPU capture')

            # Legacy callers that omit the new option retain the existing GCP route.
            legacy = args()
            del legacy.compile_host
            with contextlib.redirect_stdout(io.StringIO()):
                controller.capture(legacy)
            cloud = json.loads((root/'evidence/gcp/cfr-fixture/capture-manifest.json').read_text())
            assert cloud['compile_host'] == 'GCP' and cloud['builder_profile'] == controller.PROFILE
            assert cloud['project'] == controller.PROJECT and 'prospective_compiler' not in cloud
            assert manifest['source_sha256'] == cloud['source_sha256']
    print('PASS: exact CPU source/audit archive, non-admission identity, invalid-offer rejection, no compiler/SSH, legacy GCP capture')


if __name__ == '__main__':
    main()
