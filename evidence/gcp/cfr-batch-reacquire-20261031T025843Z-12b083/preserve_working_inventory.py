"""Record preserved local draft hashes without compiling or staging their sources."""
from pathlib import Path
import hashlib
import json
import subprocess
from datetime import datetime, timezone

root = Path(__file__).resolve().parents[3]
out = Path(__file__).resolve().parent
capture = root / 'evidence/gcp/cfr-arithmetic-frobenius-nested-charge-space-dev416-20261031T040643Z-3eefae'
manifest = json.loads((capture / 'capture-manifest.json').read_text(encoding='utf-8'))
status = subprocess.run(['git', 'status', '--porcelain=v1', '-z', '--untracked-files=all'], cwd=root, capture_output=True, check=True).stdout.decode('utf-8')
rows = []
for record in status.split('\0'):
    if not record:
        continue
    kind, name = record[:2], record[3:]
    path = root / name
    if path.is_file() and name.endswith('.lean'):
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        rows.append(dict(status=kind, path=name, sha256=digest, captured_in_never_submitted_416=manifest['source_sha256'].get(name) == digest, proof_status='Uncompiled/unaudited unless separately covered by an explicit accepted receipt; working-tree presence alone proves nothing.'))
result = dict(utc=datetime.now(timezone.utc).isoformat(), preserved_without_staging_source_edits=True, rows=rows, never_submitted_capture=capture.name, raw_git_status=status.replace('\0', '\n'))
with (out / 'working-tree-preservation-inventory.json').open('x', encoding='utf-8') as f:
    json.dump(result, f, indent=2)
    f.write('\n')
print(json.dumps(dict(lean_working_changes=len(rows), retained_in_416=sum(v['captured_in_never_submitted_416'] for v in rows))))
