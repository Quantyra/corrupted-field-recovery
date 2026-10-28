"""Optional slower replay of the original outside-promise bounded refusal."""
import json
import random
from itertools import combinations
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_recovery import fixture, ref_value, SEED, r

n, _, cert = fixture(3, True, random.Random(SEED))
cert['support'] = [sum(((column >> i) & 1) << j
                       for j, column in enumerate(cert['coordinates'])) for i in range(3)]
coefficients = [ref_value(cert, 1 << i, 1 << j, 1 << k)
                for i, j, k in combinations(range(n), 3)]
result, info = r.recover(n, coefficients, 3, 1, random.Random(SEED+3))
assert result is None
assert info['trials'] == 32768 and info['random_bits'] == 1277952
assert info['rejected'] == {'balance_dimension': 32245, 'field_generator': 523}
print(json.dumps(info, indent=2))
