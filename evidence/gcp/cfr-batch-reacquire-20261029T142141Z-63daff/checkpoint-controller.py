import gcp_cfr as c
import json
batch=c.EVIDENCE/'cfr-batch-reacquire-20261029T142141Z-63daff'
runs=[]
for path in sorted(c.EVIDENCE.glob('*/launch-request.json')):
    launch=json.loads(path.read_text())
    if launch['utc'] < '2026-10-29T14:22:21':
        continue
    run=path.parent
    terminal=run/'collected/terminal-receipt.json'
    assert (run/'collected/exit-code').is_file(), run.name
    manifest=json.loads((run/'capture-manifest.json').read_text())
    outcome=json.loads(terminal.read_text()) if terminal.is_file() else {}
    runs.append(dict(run=run.name,exit_code=(run/'collected/exit-code').read_text().strip(),
        status=outcome.get('status'),failure=outcome.get('failure'),targets=manifest['targets'],
        collected=True,root_scope_review=(run/'scope-review.json').is_file()))
c.save(batch/'checkpoint-1620.json',dict(utc=c.utc(),instance=c.VM,all_launched_outcomes_collected=True,
    STOP_ceiling_utc='2026-10-29T18:22:21.380+00:00',latest_submission_utc='2026-10-29T17:27:21.380+00:00',
    runs=runs,note='Active batch checkpoint. No queued capture or active compiler; awaiting selected author increments. VM retained under ongoing task authorization.'))
