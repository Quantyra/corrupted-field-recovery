import hashlib, importlib.util, json, tarfile
from pathlib import Path
s=importlib.util.spec_from_file_location("gcp", "tools/gcp_cfr.py")
m=importlib.util.module_from_spec(s); s.loader.exec_module(m)
run="cfr-isolated-four-sampled-identification-dev08-20261029T032959Z-1d211e"
out=m.run_directory(run); label=m.unique("collect-recovery")
expected="849052cfa50ef734ce5dcadbb39ed11fd36a8009ac0b18aa13588453d8446c69"
for name in ["cfr-collect-20261029T034804Z-524f45-package.stdout.txt","cfr-collect-20261029T034914Z-a201ea-package.stdout.txt"]:
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
m.save(out/(label+"-collection.json"),dict(run=run,utc=m.utc(),archive_sha256=expected,package_transport_failed=True,recovery="Read-only download of already packaged archive; two retained matching package stdout hashes; archive and all terminal log hashes checked",retained_sha256={p.relative_to(collected).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in collected.rglob("*") if p.is_file()}))
print("COLLECTED",run)
