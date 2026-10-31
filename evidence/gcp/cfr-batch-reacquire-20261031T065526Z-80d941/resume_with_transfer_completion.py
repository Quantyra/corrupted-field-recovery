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
run = 'cfr-balance-gaussian-array-orbit-step-dev425-20261031T075637Z-a6ce3e'
out = root / 'evidence/gcp' / run
assert not (out / 'launch-request.json').exists()
c.save(out / 'verification-completion-transport-variant.json', dict(
    utc=c.utc(), run=run, wrapper_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    controller_sha256=hashlib.sha256((root / 'tools/gcp_cfr.py').read_bytes()).hexdigest(),
    scope='Read-only verification marker and one-second SSH terminal grace only.',
    guards_and_hashes_unchanged=True, immutable_inputs_unchanged=True,
    runner_timeout_unchanged=True, launch_once_rule_unchanged=True,
    evidence='read-only transfer completion probe exited zero with all five hashes and marker verified'))
original_ssh = c.ssh
def verification_completion(script, directory, label):
    if label.endswith('-verify'):
        script += 'printf "CFR_TRANSFER_CHECKS_FINISHED\\n"\nsleep 1\n'
    return original_ssh(script, directory, label)
c.ssh = verification_completion
c.resume_prelaunch(SimpleNamespace(run=run))
