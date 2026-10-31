"""Read-only current-account, exact stopped-builder and ingress verification."""
from pathlib import Path
import json
import sys
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools'))
import gcp_cfr as c
out = Path(__file__).resolve().parent
previous = json.loads((ROOT / 'evidence/gcp/cfr-batch-reacquire-20261030T205345Z-ff4d30/final-lifecycle-verification.json').read_text(encoding='utf-8'))
assert previous['status'] == 'TERMINATED' and previous['external_access_configs_absent']
account = json.loads(c.cloud(['auth', 'list', '--filter=account:' + c.ACCOUNT, '--format=json'], out, 'same-account', flags=False))
assert len(account) == 1 and account[0]['account'] == c.ACCOUNT
vm = json.loads(c.cloud(['compute', 'instances', 'describe', c.VM, '--format=json'], out, 'initial-instance-state'))
assert vm['id'] == previous['instance_id'] == '3335066512373302615'
assert vm['status'] == 'TERMINATED'
assert vm['lastStopTimestamp'] == previous['lastStopTimestamp']
assert vm['machineType'].endswith('/e2-highmem-8')
assert int(vm['scheduling']['maxRunDuration']['seconds']) == 14400
assert vm['scheduling']['instanceTerminationAction'] == 'STOP'
assert not any(nic.get('accessConfigs') for nic in vm['networkInterfaces'])
ingress = json.loads(c.cloud(['compute', 'instances', 'network-interfaces', 'get-effective-firewalls', c.VM, '--network-interface=nic0', '--format=json'], out, 'effective-ingress'))
expected = json.loads((ROOT / 'evidence/gcp/cfr-batch-reacquire-20261030T205345Z-ff4d30/effective-ingress.stdout.txt').read_text(encoding='utf-8'))
assert ingress == expected, 'Effective ingress changed; inspect before any lifecycle mutation'
c.save(out / 'readiness.json', dict(utc=c.utc(), same_account=c.ACCOUNT, instance_id=vm['id'], status=vm['status'], machine_type='e2-highmem-8', max_run_duration_seconds=14400, stop_action='STOP', task_egress_absent=True, effective_ingress_unchanged=True, previous_stop_receipt='../cfr-batch-reacquire-20261030T205345Z-ff4d30/final-lifecycle-verification.json'))
print('READINESS_PASS_NO_START_ISSUED')
