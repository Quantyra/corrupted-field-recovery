"""Read-only probe of a transfer-completion marker after repeated Windows client faults."""
from pathlib import Path
import hashlib
import sys
import json
root = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(root / 'tools'))
import gcp_cfr as c
run = 'cfr-balance-gaussian-array-orbit-step-dev425-20261031T075637Z-a6ce3e'
out = root / 'evidence/gcp' / run
assert not (out / 'launch-request.json').exists()
names = ['inputs.tar.gz', 'capture-manifest.json', 'gcp_cfr_runner.py', 'run.sh', 'bootstrap-assets.json']
expected = {n: hashlib.sha256((out / n).read_bytes()).hexdigest() for n in names}
checks = '\n'.join(digest + '  ' + name for name, digest in expected.items())
label = c.unique('read-only-transfer-completion-probe')
script = 'set -eu\nrun="$HOME/quantyra-cfr-runs/' + run + '"\n'
script += 'test ! -e "$run/runner-pid"\ntest ! -e "$run/started-utc"\ncd "$run"\n'
script += "sha256sum -c <<'CFR_HASHES'\n" + checks + '\nCFR_HASHES\n'
script += 'printf "CFR_TRANSFER_CHECKS_FINISHED\\n"\nsleep 1\n'
raw = c.ssh(script, out, label)
assert b'CFR_TRANSFER_CHECKS_FINISHED' in raw
c.save(out / (label + '-result.json'), dict(utc=c.utc(), read_only=True, no_launch=True, sha256=expected, marker_verified=True, terminal_grace_seconds=1))
