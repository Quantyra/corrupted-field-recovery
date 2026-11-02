"""One bounded dedicated-builder start after saved read-only controls pass."""
from pathlib import Path
import json
import sys
from datetime import datetime, timedelta
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools'))
import gcp_cfr as c
out = Path(__file__).resolve().parent
ready = json.loads((out / 'readiness.json').read_text(encoding='utf-8'))
initial = json.loads((out / 'initial-instance-state.stdout.txt').read_text(encoding='utf-8'))
assert ready['status'] == 'TERMINATED' and ready['effective_ingress_unchanged'] and ready['task_egress_absent']
assert len(initial['disks']) == 1 and int(initial['disks'][0]['diskSizeGb']) == 100
assert initial['disks'][0]['source'].endswith('/quantyra-cfr-lean-builder-20261028a')
c.save(out / 'start-intent.json', dict(utc=c.utc(), project=c.PROJECT, instance=c.VM, zone=c.ZONE, account=c.ACCOUNT, instance_id=initial['id'], initial_state='TERMINATED', single_start=True, spend_scope='Existing user-authorized bounded dedicated CFR continuation; no profile expansion.'))
c.cloud(['compute', 'instances', 'start', c.VM, '--format=json'], out, 'start-task-instance')
vm = json.loads(c.cloud(['compute', 'instances', 'describe', c.VM, '--format=json'], out, 'started-instance-state'))
assert vm['id'] == '3335066512373302615' and vm['status'] == 'RUNNING'
assert vm['machineType'].endswith('/e2-highmem-8')
assert int(vm['scheduling']['maxRunDuration']['seconds']) == 14400
assert vm['scheduling']['instanceTerminationAction'] == 'STOP'
assert not any(nic.get('accessConfigs') for nic in vm['networkInterfaces'])
start = datetime.fromisoformat(vm['lastStartTimestamp'])
deadlines = dict(actual_start_utc=start.isoformat(), submission_cutoff_utc=(start+timedelta(hours=3)).isoformat(), full_stage_launch_cutoff_utc=(start+timedelta(hours=3, minutes=5)).isoformat(), automatic_stop_ceiling_utc=(start+timedelta(hours=4)).isoformat(), stage_timeout_seconds=1800, minimum_closeout_margin_after_launch_seconds=3300)
c.save(out / 'ownership.json', dict(utc=c.utc(), initial_state='TERMINATED', started_for_task=True, instance=c.VM, project=c.PROJECT, zone=c.ZONE, instance_id=vm['id'], lastStartTimestamp=vm['lastStartTimestamp'], scheduling=vm['scheduling']))
c.save(out / 'deadlines.json', deadlines)
c.save(out / 'add-egress-intent.json', dict(utc=c.utc(), absent_before=True, effective_ingress_unchanged=True, name='external-nat', task_only=True))
c.cloud(['compute', 'instances', 'add-access-config', c.VM, '--network-interface=nic0', '--access-config-name=external-nat', '--format=json'], out, 'add-task-egress')
after = json.loads(c.cloud(['compute', 'instances', 'describe', c.VM, '--format=json'], out, 'egress-instance-state'))
assert after['id'] == vm['id'] and after['status'] == 'RUNNING'
configs = [a for nic in after['networkInterfaces'] for a in nic.get('accessConfigs', [])]
assert len(configs) == 1 and configs[0]['name'] == 'external-nat'
c.save(out / 'started-lifecycle.json', dict(utc=c.utc(), instance_id=vm['id'], status='RUNNING', exact_profile_verified=True, single_start=True, task_egress_added_once=True, effective_ingress_unchanged=True, deadlines=deadlines, process_guard_pending=True))
print(json.dumps(deadlines))
