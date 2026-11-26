"""Exact two-row certificate for the 5-adic obstruction."""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from math import isqrt, lcm

TARGET = Fraction(2097, 10_000)
LIMIT = 43_000
SPECIAL = {1, 3, 9}
CORE = (7, 33, 11, 21)


def cap(prime):
    return Fraction(2) if prime == 3 else Fraction(10, 7)


@lru_cache(None)
def prime_powers(modulus):
    remainder = modulus
    factors = {}
    for prime in range(3, isqrt(modulus) + 1, 2):
        if remainder % prime == 0:
            power = 1
            while remainder % prime == 0:
                remainder //= prime
                power *= prime
            factors[prime] = power
        if remainder == 1:
            break
    if remainder > 1:
        factors[remainder] = remainder
    return factors


@lru_cache(None)
def weight(modulus):
    result = Fraction(1, modulus)
    for prime in prime_powers(modulus):
        result *= cap(prime)
    return result


def coordinate_histograms(powers):
    size = max(powers)
    # A translation lets us set one congruence at maximum depth to zero.
    fixed = powers.index(size)
    choices = [(0,) if i == fixed else range(power) for i, power in enumerate(powers)]
    histograms = set()
    for residues in product(*choices):
        masks = (
            sum(1 << i for i, (power, residue) in enumerate(zip(powers, residues))
                if x % power == residue)
            for x in range(size)
        )
        histograms.add(tuple(sorted(Counter(masks).items())))
    return size, histograms


def maximum_mass(rows):
    """Upper bound simultaneous coverage for every phase choice in the rows."""
    cofactors = [cofactor for row in rows for cofactor in row]
    factorization = [prime_powers(d) for d in cofactors]
    primes = sorted(set().union(*factorization))
    coordinates = [coordinate_histograms([f.get(p, 1) for f in factorization])
                   for p in primes]
    row_masks = []
    offset = 0
    for row in rows:
        row_masks.append(((1 << len(row)) - 1) << offset)
        offset += len(row)
    states = 1 << offset
    success = [all(mask & row for row in row_masks) for mask in range(states)]
    best = Fraction(0)
    for histograms in product(*(histograms for _, histograms in coordinates)):
        values = [Fraction(ok) for ok in success]
        for p, (size, _), histogram in reversed(list(zip(primes, coordinates, histograms))):
            next_values = []
            for mask, possible in enumerate(success):
                if not possible:
                    next_values.append(Fraction(0))
                    continue
                remaining = Fraction(1)
                bound = Fraction(0)
                # Each residue has conditional mass at most cap(p)/size.
                # Fill the groups in order of the highest admissible future mass.
                for value, count in sorted(
                    ((values[mask & group], count) for group, count in histogram),
                    reverse=True,
                ):
                    allocated = min(remaining, count * cap(p) / size)
                    bound += allocated * value
                    remaining -= allocated
                    if remaining == 0:
                        break
                next_values.append(bound)
            values = next_values
        best = max(best, values[-1])
    return best


def check():
    # W(d) <= 2/sqrt(3d), and W(d) <= W(7) for non-special d.
    minimum = TARGET - weight(7)
    assert minimum > 0 and minimum**2 * LIMIT > Fraction(4, 3)
    labels = [d for d in range(7, LIMIT + 1, 2) if d % 5 and d not in SPECIAL
              and weight(d) >= minimum]
    pairs = [pair for pair in combinations(labels, 2)
             if sum(weight(d) for d in pair) >= TARGET]
    survivors = []
    for i, left in enumerate(pairs):
        for right in pairs[i + 1:]:
            if set(left) & set(right):
                continue
            if sum(weight(lcm(a, b)) for a in left for b in right) < TARGET:
                continue
            ceiling = maximum_mass((left, right))
            if ceiling >= TARGET:
                survivors.append((left, right))
            print(left, right, ceiling)
    assert survivors == [((7, 33), (11, 21))]
    core = (CORE[:2], CORE[2:])
    ninth = maximum_mass((*core, (9,)))
    assert ninth == Fraction(2320, 33957)
    # Any partner other than 1, 3, 7 and 9 has weight at most W(21).
    assert ninth + weight(21) < TARGET
    print("Only compatible pairs:", survivors[0])
    print("Upper bound inside any class modulo 9:", ninth)


if __name__ == "__main__":
    check()
