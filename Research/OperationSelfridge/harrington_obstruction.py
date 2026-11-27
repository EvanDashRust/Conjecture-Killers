"""Exact certificate for the Harrington repair obstruction in PROOF.md."""
from fractions import Fraction as Q
from math import isqrt, prod

from harrington_seed import seed

PRIMES = (3, 5, 7, 11, 13, 17)
ALPHABETS = (Q(1), Q(18, 5), Q(32, 7), Q(9), Q(11), Q(16))
CONVEX_LAST = 2500
PRIME_LAST = 300_000
SCALE = 10**18
GROUP_SCALE = 10**12


def prime_sieve(limit):
    sieve = bytearray(b'\1') * (limit + 1)
    sieve[:2] = b'\0\0'
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            count = (limit - p*p) // p + 1
            sieve[p*p:limit+1:p] = bytes(count)
    return sieve


def ceil_ratio(numerator, denominator):
    return -(-numerator // denominator)


def scaled_ceil(x):
    return ceil_ratio(x.numerator * SCALE, x.denominator)


def effective_support_and_mass(modulus, alphabets):
    support = 0
    mass = Q(1)
    for index, (p, size) in enumerate(zip(PRIMES, alphabets)):
        if modulus % p == 0:
            modulus //= p
            mass /= size
            if p != 3 or modulus % 3 == 0:
                support |= 1 << index
            while modulus % p == 0:
                modulus //= p
                mass /= p
    assert modulus == 1
    return support, mass


def old_groups():
    size = 1 << len(PRIMES)
    weights = [Q(0)] * size
    for support in range(1, size):
        # The fixed residue modulo 3 makes exponents 0 and 1 invisible in the support.
        factor_at_3 = Q(1, 2) if support & 1 else Q(2)
        weights[support] = factor_at_3 * prod(
            Q(p, p - 1) / s if support & (1 << i) else Q(1)
            for i, (p, s) in enumerate(zip(PRIMES[1:], ALPHABETS[1:]), start=1)
        )
    for modulus, _ in seed():
        support, weight = effective_support_and_mass(modulus, ALPHABETS)
        if support:
            weights[support] -= weight
    assert all(w >= 0 for w in weights)
    return weights


def condition_single_coordinates(weights):
    # Condition away every old-only axis group other than the 3-adic axis.
    # Each remaining coordinate marginal is bounded by its old cap divided by survival.
    survival = [Q(1)] + [1 - weights[1 << i] for i in range(1, len(PRIMES))]
    assert all(s > 0 for s in survival)
    removed_axes = {1 << i for i in range(1, len(PRIMES))}
    for support in range(1, len(weights)):
        if support in removed_axes:
            weights[support] = Q(0)
        else:
            weights[support] /= prod(s for i, s in enumerate(survival) if support & (1 << i))
    return [s * prob for s, prob in zip(ALPHABETS, survival)]


def shearer_survival(weights):
    polynomials = [Q(1)]
    for universe in range(1, len(weights)):
        bit = universe & -universe
        rest = universe ^ bit
        subset = rest
        value = polynomials[rest]
        while True:
            value -= weights[subset | bit] * polynomials[rest ^ subset]
            if subset == 0:
                break
            subset = (subset - 1) & rest
        assert value > 0
        polynomials.append(value)
    return polynomials[-1]


def divisor_count_upper(alphabets, limit):
    """Outward integer bounds on the distribution of D for values up to limit."""
    mass = [0] * (limit + 1)
    mass[1] = SCALE
    for p, s in zip(PRIMES, alphabets):
        factors = [Q(0), 1 - 1/s]
        term = (1 - Q(1, p)) / s
        for _ in range(2, limit + 1):
            factors.append(term)
            term /= p
        coefficients = [(f.numerator, f.denominator) for f in factors]
        next_mass = [0] * (limit + 1)
        for d, upper in enumerate(mass[1:], start=1):
            if upper:
                for factor in range(1, limit // d + 1):
                    numerator, denominator = coefficients[factor]
                    next_mass[d * factor] += ceil_ratio(upper * numerator, denominator)
        mass = next_mass
    return mass


def fresh_sums(alphabets):
    first = prod(1 + Q(p, p - 1) / s for p, s in zip(PRIMES, alphabets))
    second = prod(1 + Q(p * (3*p - 1), (p - 1)**2) / s for p, s in zip(PRIMES, alphabets))
    first_scaled = scaled_ceil(first)
    sieve = prime_sieve(PRIME_LAST)
    mass = divisor_count_upper(alphabets, CONVEX_LAST)
    prefix, weighted = [0], [0]
    for value, probability in enumerate(mass[1:], start=1):
        prefix.append(prefix[-1] + probability)
        weighted.append(weighted[-1] + value * probability)
    small = 0
    for p in range(19, CONVEX_LAST + 1):
        if sieve[p]:
            candidates = [ceil_ratio(first_scaled - t*SCALE + t*prefix[t] - weighted[t], p - 1 - t)
                          for t in range(p - 1)]
            small += min(candidates)
    middle = sum(ceil_ratio(SCALE, (p-1)**2)
                 for p in range(CONVEX_LAST + 1, PRIME_LAST + 1) if sieve[p])
    return small, middle, second


def verify():
    weights = old_groups()
    alphabets = condition_single_coordinates(weights)
    scaled_groups = [ceil_ratio(w.numerator * GROUP_SCALE, w.denominator) for w in weights]
    old_survival = shearer_survival([Q(u, GROUP_SCALE) for u in scaled_groups])
    small, middle, second = fresh_sums(alphabets)
    fresh_loss = Q(small, SCALE) + second * (Q(middle, SCALE) + Q(1, PRIME_LAST - 1))
    print('Conditioned alphabets:', ', '.join(map(str, alphabets)))
    print(f'Guaranteed old-only survivor mass: {float(old_survival):.12f}')
    print(f'Fresh-prime blocked mass upper bound: {float(fresh_loss):.12f}')
    print(f'Combined bad mass upper bound: {float(1 - old_survival + fresh_loss):.12f}')
    assert old_survival > Q(3223, 10000)
    assert fresh_loss < Q(3223, 10000)


if __name__ == '__main__':
    verify()
