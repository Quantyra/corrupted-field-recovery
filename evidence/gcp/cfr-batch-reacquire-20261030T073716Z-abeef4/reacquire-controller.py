import sys
from pathlib import Path
sys.path.insert(0,str(Path('tools').resolve()))
import gcp_cfr as c
import json
from datetime import datetime, timedelta
out = c.EVIDENCE/'cfr-batch-reacquire-20261030T073716Z-abeef4'
initial=json.loads((out/'initial-instance.stdout.txt').read_text())
assert initial['status']=='TERMINATED' and initial['id']=='3335066512373302615'
assert initial['machineType'].endswith('/e2-highmem-8')
assert not initial['networkInterfaces'][0].get('accessConfigs')
assert initial['scheduling']['instanceTerminationAction']=='STOP' and int(initial['scheduling']['maxRunDuration']['seconds'])==14400
c.save(out/'start-intent.json',dict(utc=c.utc(),instance=c.VM,action='start same task-owned builder once'))
c.cloud(['compute','instances','start',c.VM,'--format=json'],out,'start-task-instance')
state=json.loads(c.cloud(['compute','instances','describe',c.VM,'--format=json'],out,'started-instance'))
assert state['id']=='3335066512373302615' and state['status']=='RUNNING'
assert state['scheduling']['instanceTerminationAction']=='STOP' and int(state['scheduling']['maxRunDuration']['seconds'])==14400
start=datetime.fromisoformat(state['lastStartTimestamp'])
c.save(out/'ownership.json',dict(utc=c.utc(),initial_state='TERMINATED',started_for_task=True,instance=c.VM,project=c.PROJECT,zone=c.ZONE,instance_id=state['id'],lastStartTimestamp=state['lastStartTimestamp'],scheduling=state['scheduling']))
c.save(out/'per-start-ceiling.json',dict(utc=c.utc(),effective_STOP_ceiling=(start+timedelta(hours=4)).isoformat(),latest_submission=(start+timedelta(hours=4,minutes=-55)).isoformat()))
assert not state['networkInterfaces'][0].get('accessConfigs')
c.save(out/'egress-intent.json',dict(utc=c.utc(),action='add only task-owned external-nat'))
c.cloud(['compute','instances','add-access-config',c.VM,'--network-interface=nic0','--access-config-name=external-nat','--format=json'],out,'add-task-egress')
c.cloud(['compute','instances','describe',c.VM,'--format=json'],out,'ready-instance')
print('READY_DIRECTORY='+out.name,flush=True)
