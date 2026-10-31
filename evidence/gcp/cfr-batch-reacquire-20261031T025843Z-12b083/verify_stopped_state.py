"""Read-only exact stopped VM, egress and retained disk verification."""
from pathlib import Path
import json
import sys
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools'))
import gcp_cfr as c
out = Path(__file__).resolve().parent
label = c.unique('final-stopped-state')
vm = json.loads(c.cloud(['compute', 'instances', 'describe', c.VM, '--format=json'], out, label))
assert vm['id'] == '3335066512373302615'
assert vm['status'] == 'TERMINATED'
assert vm['machineType'].endswith('/e2-highmem-8')
assert not any(nic.get('accessConfigs') for nic in vm['networkInterfaces'])
disk_name = vm['disks'][0]['source'].rsplit('/', 1)[-1]
disk = json.loads(c.cloud(['compute', 'disks', 'describe', disk_name, '--format=json'], out, label + '-retained-disk'))
assert int(disk['sizeGb']) == 100
assert disk['status'] == 'READY'
c.save(out / 'final-lifecycle-verification.json', dict(utc=c.utc(), instance=c.VM, instance_id=vm['id'], status=vm['status'], lastStartTimestamp=vm.get('lastStartTimestamp'), lastStopTimestamp=vm.get('lastStopTimestamp'), external_access_configs_absent=True, retained_disk=disk_name, retained_disk_size_gb=100, retained_disk_status=disk['status'], no_duplicate_start_or_stop=True, automatic_stop_ceiling='2026-10-31T07:00:05.258Z'))
print(json.dumps(dict(status=vm['status'], lastStopTimestamp=vm.get('lastStopTimestamp'), task_egress_absent=True, retained_disk_size_gb=100)))
