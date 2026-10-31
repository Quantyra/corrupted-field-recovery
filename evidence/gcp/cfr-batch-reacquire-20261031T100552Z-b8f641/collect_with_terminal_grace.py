"""Normal terminal collection with an SSH completion marker and brief grace.

This changes only the terminal packaging command's response completion. It does
not change runner execution, launch/ownership guards, deadlines or hash checks.
"""
from pathlib import Path
import hashlib
import sys
from types import SimpleNamespace

root = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(root / 'tools'))
import gcp_cfr as c

run = sys.argv[1]
out = c.run_directory(run)
assert (out / 'launch-request.json').is_file()
assert not (out / 'collected/exit-code').exists()
c.save(out / 'collection-terminal-grace-variant.json', dict(
    utc=c.utc(), run=run,
    wrapper_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    controller_sha256=hashlib.sha256((root / 'tools/gcp_cfr.py').read_bytes()).hexdigest(),
    scope='Terminal packaging SSH completion marker and one-second grace only.',
    normal_collection_and_log_hash_checks_unchanged=True,
    no_launch_or_runner_change=True, no_timeout_or_deadline_change=True))
original_ssh = c.ssh

def terminal_grace(script, directory, label):
    if label.endswith('-package'):
        script += 'printf "CFR_ARCHIVE_CHECKS_FINISHED\\n"\nsleep 1\n'
    return original_ssh(script, directory, label)

c.ssh = terminal_grace
c.observation(SimpleNamespace(mode='collect', run=run))
