"""Download and verify an already packaged terminal archive; never repackage or launch."""
import sys, json, hashlib, tarfile
from pathlib import Path
sys.path.insert(0, str(Path.cwd() / "tools"))
import gcp_cfr as c
run, expected = sys.argv[1:3]
out = c.run_directory(run)
label = c.unique("collect-existing-archive-recovery")
archive = out / (label + "-evidence.tar.gz")
c.save(out / (label + "-intent.json"), {"run": run, "utc": c.utc(), "action": "Download existing terminal archive only; no repackage/relaunch", "archive_sha256": expected})
c.cloud(["compute", "scp", c.scp_destination("/home/dfredriksen_quantyra_org", run) + "collected-evidence.tar.gz", str(archive), "--tunnel-through-iap"], out, label + "-download")
assert hashlib.sha256(archive.read_bytes()).hexdigest() == expected
collected = out / "collected"
with tarfile.open(archive) as tar:
    for member in tar.getmembers():
        if member.isfile():
            dest = collected / member.name
            assert dest.resolve().is_relative_to(collected.resolve())
            dest.parent.mkdir(parents=True, exist_ok=True)
            data = tar.extractfile(member).read()
            assert not dest.exists() or dest.read_bytes() == data
            dest.write_bytes(data)
receipt = json.loads((collected / "terminal-receipt.json").read_text())
for name, expected_hash in receipt["log_sha256"].items():
    assert hashlib.sha256((collected / name).read_bytes()).hexdigest() == expected_hash
c.save(out / (label + "-collection.json"), {"run": run, "utc": c.utc(), "archive_sha256": expected, "retained_sha256": {p.relative_to(collected).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in collected.rglob("*") if p.is_file()}, "recovered_existing_archive": True})
print("COLLECTED_HASH_VERIFIED", run)
