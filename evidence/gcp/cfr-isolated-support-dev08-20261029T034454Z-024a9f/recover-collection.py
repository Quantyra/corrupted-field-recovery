import hashlib, importlib.util, json, tarfile
from pathlib import Path
s=importlib.util.spec_from_file_location("gcp", "tools/gcp_cfr.py")
m=importlib.util.module_from_spec(s); s.loader.exec_module(m)
run="cfr-isolated-support-dev08-20261029T034454Z-024a9f"
out=m.run_directory(run); label=m.unique("collect-recovery")
expected="27d860b8a215028fae7d0de5ba6a9e50f909dd3962eb071e5e0e422328de6912"
for name in ["cfr-collect-20261029T035924Z-bac656-package.stdout.txt"]:
 text=(out/name).read_text(); assert expected+"  collected-evidence.tar.gz" in text; assert "CFR_HOME=/home/dfredriksen_quantyra_org" in text
archive=out/(label+"-evidence.tar.gz")
m.cloud(["compute","scp",m.scp_destination("/home/dfredriksen_quantyra_org",run)+"collected-evidence.tar.gz",str(archive),"--tunnel-through-iap"],out,label+"-download")
assert hashlib.sha256(archive.read_bytes()).hexdigest()==expected
with tarfile.open(archive) as t:
 for member in t.getmembers():
  if member.isfile():
   dest=out/"collected"/member.name
   assert dest.resolve().is_relative_to((out/"collected").resolve())
   data=t.extractfile(member).read()
   assert not dest.exists() or dest.read_bytes()==data
   dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes(data)
collected=out/"collected"; receipt=json.loads((collected/"terminal-receipt.json").read_text())
assert receipt["run"]==run
for name,h in receipt["log_sha256"].items(): assert hashlib.sha256((collected/name).read_bytes()).hexdigest()==h
m.save(out/(label+"-collection.json"),dict(run=run,utc=m.utc(),archive_sha256=expected,package_transport_failed=True,recovery="Read-only download of already packaged archive; retained package stdout hash; archive and all terminal log hashes checked",retained_sha256={p.relative_to(collected).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in collected.rglob("*") if p.is_file()}))
print("COLLECTED",run)
