"""Resume the existing prelaunch handle with a verification completion marker.

All normal controller guards, transfer hashes, immutable inputs and single-launch
intent checks remain in force. Only the read-only verification SSH script gains
a marker and one-second terminal grace period; runner/stage timeouts are unchanged.
"""
from pathlib import Path
import hashlib
import sys
from types import SimpleNamespace
root = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(root / 'tools'))
import gcp_cfr as c
run = 'cfr-arithmetic-frobenius-call-run-dev430-20261031T085743Z-43435c'
out = root / 'evidence/gcp' / run
assert not (out / 'launch-request.json').exists()
c.save(out / 'verification-completion-transport-variant.json', dict(
    utc=c.utc(), run=run, wrapper_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    controller_sha256=hashlib.sha256((root / 'tools/gcp_cfr.py').read_bytes()).hexdigest(),
    scope='Read-only verification marker and one-second SSH terminal grace only.',
    guards_and_hashes_unchanged=True, immutable_inputs_unchanged=True,
    runner_timeout_unchanged=True, launch_once_rule_unchanged=True,
    evidence='Prior425 read-only transfer-completion probe succeeded;430 normal verification failed twice after printing all five hashes OK, with no launch intent'))
original_ssh = c.ssh
def verification_completion(script, directory, label):
    if label.endswith('-verify'):
        script += 'printf "CFR_TRANSFER_CHECKS_FINISHED\\n"\nsleep 1\n'
    return original_ssh(script, directory, label)
c.ssh = verification_completion
c.resume_prelaunch(SimpleNamespace(run=run))
