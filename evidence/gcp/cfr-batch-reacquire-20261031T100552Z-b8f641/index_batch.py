"""Read-only exact fresh-batch capture/launch/collection index."""
from pathlib import Path
import json,re
from datetime import datetime,timezone
root=Path(__file__).resolve().parents[3]
out=Path(__file__).resolve().parent
rows=[]
for d in (root/'evidence/gcp').iterdir():
 match=re.search(r'-dev(\d+)-',d.name)
 if not match or not 436<=int(match.group(1)):continue
 manifest=d/'capture-manifest.json'
 row=dict(run=d.name,development_number=int(match.group(1)),captured=manifest.exists(),launched=(d/'launch-request.json').exists(),collected=(d/'collected/exit-code').exists(),accepted=(d/'root-semantic-acceptance.json').exists(),superseded_unsubmitted=(d/'superseded-unsubmitted.json').exists(),validation_failure=(d/'capture-validation-failure.json').exists())
 row['never_submitted']=(d/'never-submitted-closeout.json').exists()
 assert not row['never_submitted'] or not row['launched'],'Never-submitted receipt contradicts launch'
 if manifest.exists():row['capture_utc']=json.loads(manifest.read_text(encoding='utf-8'))['utc']
 if row['collected']:row['exit_code']=(d/'collected/exit-code').read_text().strip()
 rows.append(row)
rows.sort(key=lambda v:(v['development_number'],v['run']))
assert all(not v['launched'] or v['collected'] for v in rows),'Uncollected launch remains'
result=dict(utc=datetime.now(timezone.utc).isoformat(),rows=rows,captures=sum(v['captured'] for v in rows),launched=sum(v['launched'] for v in rows),collected=sum(v['collected'] for v in rows),accepted=sum(v['accepted'] for v in rows),superseded_unsubmitted=sum(v['superseded_unsubmitted'] for v in rows),capture_validation_failures=sum(v['validation_failure'] for v in rows),all_launched_collected=True)
result['never_submitted']=sum(v['never_submitted'] for v in rows)
with (out/'batch-run-index.json').open('x',encoding='utf-8',newline='\n') as f:json.dump(result,f,indent=2);f.write('\n')
print(json.dumps({k:v for k,v in result.items() if k!='rows'}))
