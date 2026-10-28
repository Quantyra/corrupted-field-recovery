"""Exact, bounded recovery of binary alternating trilinear tensors.

Input: n and the binomial(n,3) binary coefficients in lexicographic order.
The reader receives neither a field nor a corruption support. All accepted
certificates are checked from scratch. See manuscript/main.tex for the model.
Algebraic ancestry: Quantyra/quantyra-quantum-complexity at
d2ae8c6fc275423c2276ba82644b8993660ec684; see PROVENANCE.md.
"""
from itertools import combinations, permutations
from math import comb


def bits(x):
    while x:
        b = x & -x
        yield b.bit_length() - 1
        x ^= b


def xor(values):
    result = 0
    for value in values:
        result ^= value
    return result


def span(columns):
    pivots = {}
    for i, column in enumerate(columns):
        v, witness = column, 1 << i
        while v:
            p = v.bit_length() - 1
            if p not in pivots:
                pivots[p] = (v, witness)
                break
            row, mask = pivots[p]
            v ^= row
            witness ^= mask
    return pivots


def solve(pivots, v):
    witness = 0
    while v:
        p = v.bit_length() - 1
        if p not in pivots:
            return None
        row, mask = pivots[p]
        v ^= row
        witness ^= mask
    return witness


def image(columns):
    return tuple(v for v, _ in span(columns).values())


def nullspace(rows, width):
    pivots = {}
    for row in rows:
        while row:
            j = row.bit_length() - 1
            if j not in pivots:
                pivots[j] = row
                break
            row ^= pivots[j]
    basis = []
    for j in range(width):
        if j in pivots:
            continue
        value = 1 << j
        for p in sorted(pivots):
            if (pivots[p] & value).bit_count() & 1:
                value ^= 1 << p
        basis.append(value)
    return basis


def identity(n):
    return tuple(1 << i for i in range(n))


def action(columns, x):
    return xor(columns[j] for j in bits(x))


def compose(a, b):
    return tuple(action(a, x) for x in b)


def inverse(columns):
    pivots = span(columns)
    if len(pivots) != len(columns):
        raise ValueError('singular coordinate map')
    return tuple(solve(pivots, 1 << j) for j in range(len(columns)))


def flatten(columns):
    n = len(columns)
    return sum(c << (n*j) for j, c in enumerate(columns))


def unflatten(v, n):
    return tuple((v >> (n*j)) & ((1 << n)-1) for j in range(n))


def remainder(a, b):
    while a and a.bit_length() >= b.bit_length():
        a ^= b << (a.bit_length()-b.bit_length())
    return a


def gcd(a, b):
    while b:
        a, b = b, remainder(a, b)
    return a


def multiply(a, b, modulus):
    degree = modulus.bit_length()-1
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a >> degree:
            a ^= modulus
    return result


def irreducible(modulus):
    if type(modulus) is not int or modulus < 3:
        return False
    degree = modulus.bit_length()-1
    x = remainder(2, modulus)
    value = x
    for k in range(1, degree+1):
        value = multiply(value, value, modulus)
        if k <= degree//2 and gcd(value ^ x, modulus) != 1:
            return False
    return value == x


class Field:
    def __init__(self, modulus):
        if not irreducible(modulus):
            raise ValueError('reducible field polynomial')
        self.modulus = modulus
        self.s = modulus.bit_length()-1
        self.q = 1 << self.s

    def mul(self, a, b):
        return multiply(a, b, self.modulus)

    def trace(self, a):
        result = 0
        for _ in range(self.s):
            result ^= a
            a = self.mul(a, a)
        if result not in (0, 1):
            raise ArithmeticError('trace outside binary field')
        return result

    def det(self, x, y, z):
        return xor(self.mul(x[a], self.mul(y[b], z[c]))
                   for a, b, c in permutations(range(3)))


def validate_input(n, coefficients, rank_limit):
    if (type(n) is not int or n < 3 or n % 3
            or type(rank_limit) is not int or not 0 <= rank_limit <= n):
        raise ValueError('n=3s>0 and integer rank limit in [0,n] required')
    if (not isinstance(coefficients, (tuple, list)) or len(coefficients) != comb(n, 3)
            or any(type(c) is not int or c not in (0, 1) for c in coefficients)):
        raise ValueError('dense binary alternating coefficients required')


def tensor_rows(n, coefficients):
    rows = [[0]*n for _ in range(n)]
    for triple, c in zip(combinations(range(n), 3), coefficients):
        if c:
            for i, j, k in permutations(triple):
                rows[i][j] ^= 1 << k
    return rows


def contraction(rows, v):
    return tuple(sum(((entry & v).bit_count() & 1) << i
                     for i, entry in enumerate(row)) for row in rows)


def common_balance(forms):
    n = len(forms[0])
    def equations():
        for B in forms:
            for i in range(n):
                for j in range(i+1, n):
                    yield (B[j] << (n*i)) ^ (B[i] << (n*j))
    return nullspace(equations(), n*n)


def certify_field(n, balances, scalar):
    s = n//3
    candidate = unflatten(action(balances, scalar), n)
    powers = [identity(n)]
    for _ in range(s):
        powers.append(compose(candidate, powers[-1]))
    flat = [flatten(t) for t in powers[:-1]]
    field_span = span(flat)
    balance_span = span(balances)
    if len(field_span) != s or any(solve(balance_span, t) is None for t in flat):
        return None
    tail = solve(field_span, flatten(powers[-1]))
    if tail is None or not irreducible((1 << s) | tail):
        return None
    modulus = (1 << s) | tail
    module_columns = []
    for _ in range(3):
        current = span(module_columns)
        v = next((1 << j for j in range(n) if solve(current, 1 << j) is None), None)
        if v is None:
            return None
        module_columns.extend(action(t, v) for t in powers[:-1])
    if len(span(module_columns)) != n:
        return None
    return candidate, modulus, inverse(module_columns)


def imbalance_image(rows, T):
    n = len(T)
    # Diagonal pairs vanish: binary alternating forms are symmetric.
    return image(action(rows[j], T[i]) ^ action(rows[i], T[j])
                 for i, j in combinations(range(n), 2))


def coordinate_vectors(columns, s):
    mask = (1 << s)-1
    return [tuple((x >> (s*j)) & mask for j in range(3)) for x in columns]


def field_columns(n, field, coordinates):
    vectors = coordinate_vectors(coordinates, field.s)
    determinants = [field.det(vectors[i], vectors[j], vectors[k])
                    for i, j, k in combinations(range(n), 3)]
    return [sum(field.trace(field.mul(1 << b, d)) << i
                for i, d in enumerate(determinants)) for b in range(field.s)]


def residual_columns(n, support):
    columns = []
    for a, b, c in combinations(range(len(support)), 3):
        u = [support[a], support[b], support[c]]
        packed = 0
        for pos, triple in enumerate(combinations(range(n), 3)):
            coefficient = 0
            for i, j, k in permutations(triple):
                coefficient ^= ((u[0] >> i) & (u[1] >> j) & (u[2] >> k) & 1)
            packed |= coefficient << pos
        columns.append(packed)
    return columns


def verify(n, coefficients, rank_limit, certificate):
    """Total Boolean checker for serialized certificates; no discovery state used."""
    try:
        validate_input(n, coefficients, rank_limit)
        if not isinstance(certificate, dict) or set(certificate) != {
                'modulus', 'coordinates', 'coefficient', 'support', 'residual'}:
            return False
        modulus = certificate['modulus']
        if type(modulus) is not int or modulus.bit_length() != n//3+1:
            return False
        field = Field(modulus)
        coordinates = certificate['coordinates']
        support = certificate['support']
        c = certificate['coefficient']
        residual = certificate['residual']
        if (not isinstance(coordinates, (list, tuple)) or len(coordinates) != n
                or not isinstance(support, (list, tuple)) or len(support) > rank_limit
                or any(type(x) is not int or x < 0 or x.bit_length() > n
                       for x in tuple(coordinates)+tuple(support))
                or type(c) is not int or not 0 < c < field.q
                or type(residual) is not int or residual < 0
                or residual.bit_length() > comb(len(support), 3)
                or len(span(coordinates)) != n or len(span(support)) != len(support)):
            return False
        compatible = action(field_columns(n, field, coordinates), c)
        error = action(residual_columns(n, support), residual)
        return compatible ^ error == sum(b << i for i, b in enumerate(coefficients))
    except (ValueError, TypeError, KeyError, IndexError, OverflowError):
        return False


def recover(n, coefficients, rank_limit, h, rng):
    """At most 8*2**(4R)*h trials; exactly 4n+s random bits per attempted trial.

    Mathematical guarantee assumes independent fair bits. A seeded RNG is only
    a reproducible test tape. Returns (certificate or None, accounting).
    Malformed inputs raise ValueError before any random draw.
    """
    validate_input(n, coefficients, rank_limit)
    if type(h) is not int or h < 1:
        raise ValueError('positive integer confidence required')
    s = n//3
    limit = 8*(1 << (4*rank_limit))*h
    rows = tensor_rows(n, coefficients)
    target = sum(b << i for i, b in enumerate(coefficients))
    rejected = {}
    def metadata(trials, reason):
        return dict(reason=reason, trials=trials, trial_limit=limit,
                    random_bits=(4*n+s)*trials, random_bit_limit=(4*n+s)*limit,
                    sufficient_field_size=s >= 2*rank_limit+5,
                    rejected=dict(rejected))
    for trial in range(1, limit+1):
        vectors = [rng.getrandbits(n) for _ in range(4)]
        scalar = rng.getrandbits(s)
        if any(type(v) is not int or not 0 <= v < 1 << n for v in vectors) or (
                type(scalar) is not int or not 0 <= scalar < 1 << s):
            raise ValueError('random tape returned an out-of-range value')
        balances = common_balance([contraction(rows, v) for v in vectors])
        reason = 'balance_dimension'
        if len(balances) == s:
            reason = 'missing_identity'
            if solve(span(balances), flatten(identity(n))) is not None:
                result = certify_field(n, balances, scalar)
                reason = 'field_generator'
                if result is not None:
                    T, modulus, coordinates = result
                    support = imbalance_image(rows, T)
                    reason = 'support_rank'
                    if len(support) <= rank_limit:
                        field = Field(modulus)
                        columns = field_columns(n, field, coordinates)
                        columns += residual_columns(n, support)
                        solution = solve(span(columns), target)
                        reason = 'coefficient_fit'
                        if solution is not None:
                            certificate = dict(modulus=modulus, coordinates=list(coordinates),
                                               coefficient=solution & (field.q-1),
                                               support=list(support), residual=solution >> s)
                            reason = 'verification'
                            if verify(n, coefficients, rank_limit, certificate):
                                return certificate, metadata(trial, 'verified')
        rejected[reason] = rejected.get(reason, 0)+1
    return None, metadata(limit, 'bounded_failure')
