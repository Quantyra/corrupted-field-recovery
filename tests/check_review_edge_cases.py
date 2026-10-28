"""Reproduce full-support and degree-one cases from the cross-provider review.

The s=1, R=n=3 input is outside the recovery probability promise. It tests
only exact acceptance soundness, which does not require a proper support.
"""
from copy import deepcopy
from itertools import permutations, product
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'src'))
from recovery import irreducible, verify


def determinant_f2(x, y, z):
    value = 0
    for i, j, k in permutations(range(3)):
        value ^= ((x >> i) & 1) * ((y >> j) & 1) * ((z >> k) & 1)
    return value


def main():
    # K=F2[X]/(X+1), identity coordinates, c=1, and E=det on full support.
    # Over F2, det + det = 0 on every triple, so this is a valid certificate
    # for the zero tensor with a nonzero compatible coefficient.
    certificate = dict(modulus=0b11, coordinates=[1, 2, 4], coefficient=1,
                       support=[1, 2, 4], residual=1)
    assert verify(3, [0], 3, certificate)
    pointwise = 0
    for x, y, z in product(range(8), repeat=3):
        compatible = determinant_f2(x, y, z)
        error = determinant_f2(x, y, z)
        assert compatible ^ error == 0
        pointwise += 1
    assert determinant_f2(1, 2, 4) == 1
    zero_coefficient = deepcopy(certificate)
    zero_coefficient['coefficient'] = 0
    assert not verify(3, [0], 3, zero_coefficient)
    assert not verify(3, [0], 2, certificate)
    assert not verify(3, [1], 3, certificate)
    # Claude identified that the published Python guard rejected X despite
    # its degree-one irreducibility. Both F2 presentations must be accepted.
    assert irreducible(2) and irreducible(3)
    assert all(not irreducible(p) for p in [0, 1, 4, 5, 6, True])
    x_modulus = deepcopy(certificate)
    x_modulus['modulus'] = 2
    assert verify(3, [0], 3, x_modulus)
    clean_x = dict(modulus=2, coordinates=[1, 2, 4], coefficient=1,
                   support=[], residual=0)
    assert verify(3, [1], 0, clean_x)
    assert not verify(3, [0], 0, clean_x)
    paths = ['src/recovery.py', 'tests/check_review_edge_cases.py']
    receipt = dict(status='passed', command='python tests/check_review_edge_cases.py',
                   python=sys.version, scope='Outside-promise degree-one and full-support certificate semantics; no recovery or uniqueness claim.',
                   n=3, s=1, rank_limit=3, coefficient=1,
                   sufficient_promise=False, pointwise_triples=pointwise,
                   checks=['valid full-support cancellation certificate accepted',
                           'compatible form independently nonzero',
                           'zero compatible coefficient rejected',
                           'insufficient support cap rejected',
                           'altered tensor rejected',
                           'both degree-one irreducible field presentations accepted',
                           'constant and reducible polynomials rejected',
                           'p=X certificates checked for clean and full-support cases'],
                   source_sha256={p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest()
                                  for p in paths})
    (ROOT/'artifacts/review-edge-cases.json').write_text(json.dumps(receipt, indent=2)+'\n',
                                                      encoding='utf-8', newline='\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
