"""Read-only full workload/lock guard after the fresh dedicated VM start."""
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools'))
import gcp_cfr as c
out = Path(__file__).resolve().parent
assert (out / 'started-lifecycle.json').is_file()
label = c.unique('initial-full-process-guard')
script = 'set -eu\nps -ww -eo user,pid,ppid,lstart,args\nprintf "\\nACTIVE_PROOF_PROCESSES\\n"\npgrep -a -x lean || true\npgrep -a -x lake || true\nflock -n "$HOME/quantyra-cfr-runs/' + c.CAMPAIGN + '/lock" true\nprintf "CAMPAIGN_LOCK_FREE\\n"\n'
c.ssh(script, out, label)
print('INVENTORY_RECEIPT=' + label)
