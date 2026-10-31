"""Read-only accepted-source verification; does not invoke Lean or cloud operations."""
import hashlib
import json
from pathlib import Path
import subprocess
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[3]
OUT = Path(__file__).resolve().parent
base = json.loads((ROOT / 'evidence/gcp/cfr-batch-reacquire-20261030T133538Z-653a99/reauth-accepted-source-snapshot.json').read_text(encoding='utf-8'))
latest = {v['source'].replace('\\', '/'): dict(v) for v in base['latest_accepted_sources']}
for receipt in (ROOT / 'evidence/gcp').glob('*/root-semantic-acceptance.json'):
    v = json.loads(receipt.read_text(encoding='utf-8'))
    if not v.get('accepted') or not isinstance(v.get('source'), str):
        continue
    manifest = json.loads((receipt.parent / 'capture-manifest.json').read_text(encoding='utf-8'))
    source = v['source'].replace('\\', '/')
    entry = dict(source=source, sha256=v['sha256'].lower(), accepted_run=receipt.parent.name, capture_utc=manifest['utc'])
    if entry['capture_utc'] >= latest.get(source, {}).get('capture_utc', ''):
        latest[source] = entry
rows = []
for source, v in sorted(latest.items()):
    v = {k: value for k, value in v.items() if k not in ['working_matches', 'head_matches']}
    v['working_matches'] = hashlib.sha256((ROOT / source).read_bytes()).hexdigest() == v['sha256']
    head = subprocess.run(['git', 'show', 'HEAD:' + source], cwd=ROOT, capture_output=True, check=True).stdout
    v['head_matches'] = hashlib.sha256(head).hexdigest() == v['sha256']
    rows.append(v)
result = dict(utc=datetime.now(timezone.utc).isoformat(), scope='Union of prior accepted-source snapshot and later explicit Root acceptance receipts; uncompiled preservation drafts excluded.', latest_accepted_sources=rows, all_working_and_head_match=all(v['working_matches'] and v['head_matches'] for v in rows))
target = OUT / 'final-accepted-source-verification.json'
with target.open('x', encoding='utf-8', newline='\n') as f:
    json.dump(result, f, indent=2)
    f.write('\n')
print(json.dumps(dict(sources=len(rows), all_working_and_head_match=result['all_working_and_head_match'], mismatches=[v['source'] for v in rows if not v['working_matches'] or not v['head_matches']])))
