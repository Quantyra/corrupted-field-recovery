import tarfile, subprocess, hashlib
from pathlib import Path
run=Path('evidence/gcp/cfr-candidate-modulus-dev37-20261029T145840Z-15d565')
name='CorruptedFieldRecovery/RawPolynomialIrreducibility.lean'
with tarfile.open(run/'inputs.tar.gz') as archive:
    data=archive.extractfile(name).read()
assert hashlib.sha256(data).hexdigest()=='9535634b8e1bd7ef0595dd85d7949d2e030f177c71cae031b30ceeede7426425'
blob=subprocess.check_output(['git','hash-object','-w','--stdin'],input=data).decode().strip()
subprocess.run(['git','update-index','--cacheinfo','100644',blob,name],check=True)
print('Staged exact accepted dev37 source; worktree successor preserved')
