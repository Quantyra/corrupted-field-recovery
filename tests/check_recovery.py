"""Reproducible finite checks, not an empirical proof of the probability theorem."""
import copy
from fractions import Fraction
import hashlib
from itertools import combinations, permutations
import json
from pathlib import Path
import platform
import random
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
import recovery as r

SEED = 20261028


class Tape:
    def __init__(self, values=None):
        self.values = None if values is None else iter(values)
        self.widths = []

    def getrandbits(self, width):
        self.widths.append(width)
        return 0 if self.values is None else next(self.values)


def ref_mul(a, b, modulus):
    # Carryless product followed by long division, independent of production.
    product = 0
    for j in range(b.bit_length()):
        if b & (1 << j):
            product ^= a << j
    for j in range(product.bit_length()-1, modulus.bit_length()-2, -1):
        if product & (1 << j):
            product ^= modulus << (j-modulus.bit_length()+1)
    return product


def ref_trace(a, modulus):
    total = a
    for _ in range(modulus.bit_length()-2):
        a = ref_mul(a, a, modulus)
        total ^= a
    assert total in (0, 1)
    return total


def ref_det(x, y, z, mul):
    return mul(x[0], mul(y[1], z[2]) ^ mul(y[2], z[1])) ^ \
        mul(x[1], mul(y[0], z[2]) ^ mul(y[2], z[0])) ^ \
        mul(x[2], mul(y[0], z[1]) ^ mul(y[1], z[0]))


def ref_value(certificate, x, y, z):
    modulus = certificate['modulus']
    s = modulus.bit_length()-1
    def coords(v):
        w = r.action(certificate['coordinates'], v)
        return [(w >> (s*j)) & ((1 << s)-1) for j in range(3)]
    mul = lambda a, b: ref_mul(a, b, modulus)
    det = ref_det(coords(x), coords(y), coords(z), mul)
    result = ref_trace(mul(certificate['coefficient'], det), modulus)
    support = certificate['support']
    for p, indices in enumerate(combinations(range(len(support)), 3)):
        if certificate['residual'] >> p & 1:
            vs = [[(support[j] & v).bit_count() & 1 for j in indices] for v in (x, y, z)]
            result ^= ref_det(*vs, lambda a, b: a & b)
    return result


def tensor_value(n, coefficients, x, y, z):
    result = 0
    for indices, c in zip(combinations(range(n), 3), coefficients):
        if c:
            for i, j, k in permutations(indices):
                result ^= ((x >> i) & (y >> j) & (z >> k) & 1)
    return result


def fixture(s, corrupted, rng, change=True):
    modulus = next(p for p in range((1 << s)|1, 1 << (s+1), 2) if r.irreducible(p))
    n = 3*s
    coordinates = list(r.identity(n))
    if change:
        for _ in range(5*n):
            i, j = rng.sample(range(n), 2)
            coordinates[i] ^= coordinates[j]
    # Pull back three covectors in the first K coordinate.
    positions = (0, s, 2*s) if s == 3 else (0, 1, 2)
    support = [sum(((column >> i) & 1) << j for j, column in enumerate(coordinates))
               for i in positions] if corrupted else []
    cert = dict(modulus=modulus, coordinates=coordinates, coefficient=1,
                support=support, residual=int(corrupted))
    coefficients = [ref_value(cert, 1 << i, 1 << j, 1 << k)
                    for i, j, k in combinations(range(n), 3)]
    return n, coefficients, cert


def scalar_matrix(cert, t):
    field = r.Field(cert['modulus'])
    inv = r.inverse(cert['coordinates'])
    def apply(v):
        c = r.action(cert['coordinates'], v)
        out = sum(field.mul((c >> (field.s*j)) & (field.q-1), t) << (field.s*j)
                  for j in range(3))
        return r.action(inv, out)
    return tuple(apply(1 << i) for i in range(len(inv)))


def good_tape(n, coefficients, cert, rng):
    # Fixture-assisted lemma tape, explicitly not ordinary sampling evidence.
    rows = r.tensor_rows(n, coefficients)
    while True:
        vectors = []
        while len(vectors) < 4:
            v = rng.getrandbits(n)
            if all((u & v).bit_count() % 2 == 0 for u in cert['support']):
                vectors.append(v)
        balances = r.common_balance([r.contraction(rows, v) for v in vectors])
        if len(balances) != n//3:
            continue
        for scalar in range(1, 1 << (n//3)):
            found = r.certify_field(n, balances, scalar)
            if found is not None:
                T, _, _ = found
                if r.span(r.imbalance_image(rows, T)).keys() == r.span(cert['support']).keys():
                    U = r.imbalance_image(rows, T)
                    if all(r.solve(r.span(U), u) is not None for u in cert['support']):
                        return vectors + [scalar], balances


def main():
    started = time.monotonic()
    rng = random.Random(SEED)
    receipt = dict(seed=SEED, python=sys.version, platform=platform.platform(),
                   command='python tests/check_recovery.py', cases=[], limitations=[
                       'Finite tests do not prove the asymptotic or probability theorem.',
                       'Seeded PRNG tests are not the independent-fair-bit model.',
                       'Scripted large-field tapes use fixture support only in the test harness.',
                       'No formal equivalence between Python and Lean is established.'])
    probability_cases = 0
    for R in range(25):
        for s in range(2*R+5, 2*R+13):
            q = 1 << s
            tau = sum(1 << d for d in range(1, s) if s % d == 0)
            beta = (1 << R)*(Fraction(1+q+q*q, q**3)+Fraction(tau, q))
            gamma = 1-Fraction(tau+(1 << (2*R))-1, q)
            assert beta < Fraction(1, 2) and gamma >= Fraction(1, 4)
            probability_cases += 1
    receipt['probability_cases'] = probability_cases
    fixtures = {}
    for s, corrupted in ((3, True), (5, False), (5, True), (7, True), (11, True)):
        fixtures[s, corrupted] = fixture(s, corrupted, rng)
    for s, corrupted, mode in ((5, False, 'ordinary_seeded'), (3, True, 'ordinary_seeded'),
                                (7, True, 'scripted'), (11, True, 'scripted')):
        n, coefficients, planted = fixtures[s, corrupted]
        R = 3 if corrupted else 0
        if mode == 'scripted':
            values, balances = good_tape(n, coefficients, planted, rng)
            tape = Tape(values)
        else:
            tape = random.Random(SEED+s)
        cert, info = r.recover(n, coefficients, R, 1, tape)
        assert cert is not None and r.verify(n, coefficients, R, cert), info
        assert info['trials'] <= info['trial_limit']
        assert info['random_bits'] == (4*n+s)*info['trials']
        if mode == 'scripted':
            assert tape.widths == [n]*4+[s]
        for _ in range(32):
            vectors = [rng.getrandbits(n) for _ in range(3)]
            assert ref_value(cert, *vectors) == tensor_value(n, coefficients, *vectors)
        for field, value in [('coefficient', 0), ('modulus', 1 << s),
                             ('coordinates', [0]*n), ('support', [1 << n]),
                             ('residual', -1)]:
            bad = copy.deepcopy(cert)
            bad[field] = value
            assert not r.verify(n, coefficients, R, bad)
        changed = list(coefficients)
        changed[0] ^= 1
        assert not r.verify(n, changed, R, cert)
        if corrupted:
            assert not r.verify(n, coefficients, 2, cert)
        receipt['cases'].append(dict(s=s, rank_limit=R, mode=mode, **info))
        print('passed recovery', s, R, mode, info['trials'], flush=True)
    # Nine supplied clean-quadruple field identifications, with hidden coordinates.
    count = 0
    for s in (5, 7, 11):
        n, coefficients, cert = fixtures[s, True]
        for _ in range(3):
            values, balances = good_tape(n, coefficients, cert, rng) if s != 5 else (None, None)
            if s == 5:
                rows = r.tensor_rows(n, coefficients)
                while True:
                    vs = []
                    while len(vs) < 4:
                        v = rng.getrandbits(n)
                        if all((u & v).bit_count() % 2 == 0 for u in cert['support']):
                            vs.append(v)
                    balances = r.common_balance([r.contraction(rows, v) for v in vs])
                    if len(balances) == s:
                        break
            actual = r.span(r.flatten(scalar_matrix(cert, 1 << j)) for j in range(s))
            assert len(actual) == s and all(r.solve(actual, b) is not None for b in balances)
            count += 1
    receipt['four_contraction_lemma_cases'] = count
    count = 0
    for s, target in ((5, 0), (7, 48), (11, 56)):
        n, coefficients, cert = fixtures[s, True]
        rows = r.tensor_rows(n, coefficients)
        found = 0
        for t in range(1 << s):
            T = scalar_matrix(cert, t)
            transpose_support = tuple(sum(((u & col).bit_count() & 1) << j
                                          for j, col in enumerate(T)) for u in cert['support'])
            independent = len(r.span(cert['support']+list(transpose_support))) == 6
            if s == 5:
                assert not independent
            if independent:
                U = r.imbalance_image(rows, T)
                assert len(U) == 3 and all(r.solve(r.span(U), u) is not None for u in cert['support'])
                found += 1
                if found == target:
                    break
        assert found == target
        count += found
    receipt['two_translate_lemma_cases'] = count
    receipt['small_field_negative'] = 's=5: all 32 scalars fail six-covector independence'
    n, coefficients, _ = fixtures[5, False]
    zeros = Tape()
    cert, info = r.recover(n, coefficients, 0, 2, zeros)
    assert cert is None and info['trials'] == 16
    assert info['random_bits'] == sum(zeros.widths) == (4*n+5)*16
    receipt['bounded_failure'] = info
    malformed = [(14, coefficients, 0, 1), (n, coefficients[:-1], 0, 1),
                 (n, [True]*len(coefficients), 0, 1), (n, coefficients, -1, 1),
                 (n, coefficients, 0, 0)]
    for args in malformed:
        tape = Tape()
        try:
            r.recover(*args, tape)
            raise AssertionError('malformed input accepted')
        except ValueError:
            assert not tape.widths
    receipt['malformed_cases'] = len(malformed)
    receipt['source_sha256'] = {str(p.relative_to(ROOT)).replace('\\', '/'):
        hashlib.sha256(p.read_bytes()).hexdigest() for p in
        [ROOT/'src/recovery.py', Path(__file__)]}
    receipt['elapsed_seconds'] = round(time.monotonic()-started, 3)
    receipt['status'] = 'passed'
    destination = ROOT/'artifacts/recovery-checks.json'
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
