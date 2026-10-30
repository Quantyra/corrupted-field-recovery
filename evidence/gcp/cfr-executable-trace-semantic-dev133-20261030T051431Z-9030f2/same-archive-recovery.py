import sys,json,hashlib,tarfile
from pathlib import Path
sys.path.insert(0,str(Path('tools').resolve()));import gcp_cfr as c
run='cfr-executable-trace-semantic-dev133-20261030T051431Z-9030f2';out=c.EVIDENCE/run
label=c.unique('collection-same-archive-recovery')
archive=out/(label+'-evidence.tar.gz')
expected='77209b461cb119c6ba23a009e25eac56b5bad8b402dd4e34db7d102a69fa1d3c'
c.cloud(['compute','scp',c.scp_destination('/home/dfredriksen_quantyra_org',run)+'collected-evidence.tar.gz',str(archive),'--tunnel-through-iap'],out,label+'-download')
assert hashlib.sha256(archive.read_bytes()).hexdigest()==expected
collected=out/'collected'
with tarfile.open(archive) as t:
 for m in t.getmembers():
  if m.isfile():
   p=collected/m.name;assert p.resolve().is_relative_to(collected.resolve())
   data=t.extractfile(m).read();assert not p.exists() or p.read_bytes()==data
   p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
receipt=json.loads((collected/'terminal-receipt.json').read_text())
for n,h in receipt['log_sha256'].items():assert hashlib.sha256((collected/n).read_bytes()).hexdigest()==h
c.save(out/(label+'-collection.json'),{'run':run,'utc':c.utc(),'archive_sha256':expected,'recovered_from':'cfr-collect-20261030T051820Z-939e24-package','package_transport_exit':3221225477,'all_terminal_log_hashes_verified':True,'retained_sha256':{p.relative_to(collected).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in collected.rglob('*') if p.is_file()}})
print('COLLECTED',run)
