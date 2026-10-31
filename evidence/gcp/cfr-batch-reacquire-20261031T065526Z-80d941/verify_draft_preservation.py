"""Verify current proof bytes against the immutable final capture, without Lean."""
from pathlib import Path
import hashlib
import json
import subprocess
import tarfile
from datetime import datetime, timezone

root = Path(__file__).resolve().parents[3]
out = Path(__file__).resolve().parent
run = 'cfr-balance-gaussian-array-orbit-append-dev435-20261031T094449Z-f211d1'
archive = root / 'evidence/gcp' / run / 'inputs.tar.gz'
rows = []
with tarfile.open(archive) as tar:
    for path in sorted((root / 'CorruptedFieldRecovery').rglob('*.lean')):
        name = path.relative_to(root).as_posix()
        current = path.read_bytes()
        captured = tar.extractfile(name).read()
        assert current == captured, name
        rows.append(dict(path=name, sha256=hashlib.sha256(current).hexdigest()))
status = subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=all'], cwd=root).decode('utf-8')
receipt = dict(utc=datetime.now(timezone.utc).isoformat(), archive_run=run,
               archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),
               all_current_main_proof_bytes_preserved=True, source_count=len(rows), sources=rows,
               working_status=status, unrelated_changes_left_unstaged=True,
               scope='Preservation only. Unaccepted source bytes remain uncompiled/unaudited drafts; no certification inferred.',
               prior_scratch_preservation='cfr-batch-reacquire-20261031T025843Z-12b083/unsubmitted-working-scratch-v2.zip')
with (out / 'final-draft-preservation.json').open('x', encoding='utf-8', newline='\n') as f:
    json.dump(receipt, f, indent=2)
    f.write('\n')
print('PRESERVED', len(rows), 'main proof source files in', run)
