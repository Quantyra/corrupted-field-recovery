"""Recover an already-packaged terminal archive after a transport failure."""
import hashlib
import json
import sys
import tarfile

import gcp_cfr as c

run, expected = sys.argv[1:]
out = c.run_directory(run)
label = c.unique('recover-collected-archive')
archive = out / (label + '.tar.gz')
c.cloud(['compute', 'scp',
         c.scp_destination('/home/dfredriksen_quantyra_org', run) + 'collected-evidence.tar.gz',
         str(archive), '--tunnel-through-iap'], out, label + '-download')
assert hashlib.sha256(archive.read_bytes()).hexdigest() == expected
with tarfile.open(archive) as tar:
    for member in tar.getmembers():
        if not member.isfile():
            continue
        dest = out / 'collected' / member.name
        assert dest.resolve().is_relative_to((out / 'collected').resolve())
        dest.parent.mkdir(parents=True, exist_ok=True)
        data = tar.extractfile(member).read()
        assert not dest.exists() or dest.read_bytes() == data
        dest.write_bytes(data)
receipt = json.loads((out / 'collected/terminal-receipt.json').read_text())
for name, sha in receipt['log_sha256'].items():
    assert hashlib.sha256((out / 'collected' / name).read_bytes()).hexdigest() == sha
c.save(out / (label + '-collection.json'), dict(
    utc=c.utc(), run=run, archive_sha256=expected,
    recovered_after_transport_failure=True,
    retained_sha256={p.relative_to(out / 'collected').as_posix():
                    hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in (out / 'collected').rglob('*') if p.is_file()}))
print('COLLECTED', run)
