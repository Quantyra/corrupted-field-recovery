"""Index immutable captures and collected outcomes; no compilation or cloud calls."""
from pathlib import Path
import json
import re
from datetime import datetime, timezone
ROOT = Path(__file__).resolve().parents[3]
OUT = Path(__file__).resolve().parent
rows = []
for manifest_path in (ROOT / 'evidence/gcp').glob('*/capture-manifest.json'):
    match = re.search(r'-dev(\d+)-', manifest_path.parent.name)
    if not match or not 317 <= int(match.group(1)) <= 354:
        continue
    directory = manifest_path.parent
    manifest = json.loads(manifest_path.read_text(encoding='utf-8'))
    receipt = json.loads((directory / 'collected/terminal-receipt.json').read_text(encoding='utf-8'))
    assert (directory / 'collected/exit-code').is_file()
    acceptance = directory / 'root-semantic-acceptance.json'
    rows.append(dict(number=int(match.group(1)), run=directory.name, capture_utc=manifest['utc'], targets=manifest['targets'], archive_sha256=manifest['archive_sha256'], terminal_status=receipt.get('status'), failure=receipt.get('failure'), warnings=receipt.get('owned_warning_headers', []), root_accepted=acceptance.is_file() and json.loads(acceptance.read_text(encoding='utf-8')).get('accepted') is True, collected=True))
rows.sort(key=lambda v:v['number'])
assert [v['number'] for v in rows] == list(range(317,355))
result = dict(utc=datetime.now(timezone.utc).isoformat(), started_utc='2026-10-30T20:54:44.324Z', submission_cutoff='2026-10-30T23:54:44.324Z', final_submission=rows[-1]['run'], fresh_launched_runs=len(rows), root_accepted_runs=sum(v['root_accepted'] for v in rows), recovered_prior_run='cfr-balance-gaussian-used-rows-dev316-20261030T154555Z-f1b120', no_local_lean_or_lake=True, runs=rows)
with (OUT / 'batch-run-index.json').open('x', encoding='utf-8', newline='\n') as f:
    json.dump(result, f, indent=2)
    f.write('\n')
print(json.dumps(dict(launched=len(rows), root_accepted=result['root_accepted_runs'], all_collected=True)))
