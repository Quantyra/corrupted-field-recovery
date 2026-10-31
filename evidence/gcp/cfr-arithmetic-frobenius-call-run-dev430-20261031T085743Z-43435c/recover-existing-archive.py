from pathlib import Path
import sys,hashlib,json,tarfile
sys.path.insert(0,str(Path.cwd()/'tools'))
import gcp_cfr as c
run='cfr-arithmetic-frobenius-call-run-dev430-20261031T085743Z-43435c'
out=c.run_directory(run)
label=c.unique('recover-existing-archive')
expected='377a5d17e47ca12eda1db9c2838f7e7e10e79fe404b2e0c2c90b00919a140388'
archive=out/(label+'-evidence.tar.gz')
c.cloud(['compute','scp',c.scp_destination('/home/dfredriksen_quantyra_org',run)+'collected-evidence.tar.gz',str(archive),'--tunnel-through-iap'],out,label+'-download')
assert hashlib.sha256(archive.read_bytes()).hexdigest()==expected
collected=out/'collected'
with tarfile.open(archive) as tar:
 for member in tar.getmembers():
  if member.isfile():
   dest=collected/member.name
   assert dest.resolve().is_relative_to(collected.resolve())
   data=tar.extractfile(member).read()
   assert not dest.exists() or dest.read_bytes()==data
   dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
r=json.loads((collected/'terminal-receipt.json').read_text(encoding='utf-8'))
for name,h in r['log_sha256'].items():assert hashlib.sha256((collected/name).read_bytes()).hexdigest()==h
c.save(out/(label+'-collection.json'),dict(run=run,utc=c.utc(),archive_sha256=expected,recovered_existing_remote_archive=True,no_repackage=True,all_terminal_log_hashes_verified=True))
print('COLLECTED EXISTING',run)
