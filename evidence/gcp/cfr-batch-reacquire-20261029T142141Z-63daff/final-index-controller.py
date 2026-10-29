import gcp_cfr as c
import json
batch=c.EVIDENCE/'cfr-batch-reacquire-20261029T142141Z-63daff'
final=c.EVIDENCE/'cfr-raw-field-coordinates-dev61-20261029T170359Z-333eff'
shutdown=json.loads((final/'cfr-shutdown-20261029T171115Z-fe47bf-result.json').read_text())
assert shutdown['stop_verified'] and shutdown['final_state']=='TERMINATED'
runs=[]
for path in sorted(c.EVIDENCE.glob('*/launch-request.json')):
    launch=json.loads(path.read_text())
    if launch['utc'] < '2026-10-29T14:22:21':
        continue
    run=path.parent
    assert (run/'collected/exit-code').is_file(), run.name
    outcome=json.loads((run/'collected/terminal-receipt.json').read_text())
    runs.append(dict(run=run.name,exit_code=(run/'collected/exit-code').read_text().strip(),
        status=outcome.get('status'),failure=outcome.get('failure'),
        collected=True,root_scope_review=(run/'scope-review.json').is_file()))
c.save(batch/'batch-summary.json',dict(utc=c.utc(),instance=c.VM,all_launched_outcomes_collected=True,
    final_state=shutdown['final_state'],stop_verified=True,persistent_cache_retained=True,
    task_egress_removed=True,no_unrelated_workload_observed=True,queued_captures=[],runs=runs,
    shutdown_receipt=str((final/'cfr-shutdown-20261029T171115Z-fe47bf-result.json').relative_to(c.EVIDENCE)).replace('\\','/'),
    note='Superseded unlaunched coordinate54 and trace32 captures remain preserved with explicit dispositions. The never-started dev25 handle was never relaunched.'))
