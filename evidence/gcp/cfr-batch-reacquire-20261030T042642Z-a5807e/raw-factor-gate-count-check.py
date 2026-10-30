import json,hashlib
from pathlib import Path
p=Path("CorruptedFieldRecovery/RawFieldCandidate.lean")
rows=[]
for s in range(11):
 count=sum(1 for d in range(1,s//2+1) for g in range(2**d,2**(d+1)) for q in range(2**(s-d+1)))
 formula=(s//2)*2**(s+1)
 assert count==formula
 rows.append(dict(s=s,explicit_enumerated_factor_pairs=count,formula=formula))
print(json.dumps(dict(source=str(p),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),source_lines="40-43,54-63",pair_space_formula="floor(s/2) * 2^(s+1)",derivation="For each d in 1..floor(s/2), g interval cardinality is 2^d and q range cardinality is 2^(s-d+1); their product is 2^(s+1).",checks=rows,scope="Exact logical factor-pair search-space count from source; finite Python enumeration checks s=0..10. Not a Lean proof or a measured primitive-bit runtime theorem. Early rejection may skip pairs. The full logical search space is exponential in s; no polynomial primitive-bit runtime theorem follows. Actual evaluation/short-circuit behavior is not measured or proved here."),indent=2))
