"""Exact two-row certificate for the 5-adic obstruction."""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from math import isqrt, lcm

from three_free_loss import FIVE_PAIR_SCHEDULE

TARGET = Fraction(2097, 10_000)
ADJUSTED_TARGET = Fraction(2085, 10_000)
LIMIT = 43_000
ADJUSTED_LIMIT = 70_000
SPECIAL = {1, 3, 9}
CORE = (7, 33, 11, 21)


def cap(prime, adjusted=False):
    if prime == 3:
        return Fraction(2)
    if adjusted and prime in FIVE_PAIR_SCHEDULE:
        return 1 / (1 - FIVE_PAIR_SCHEDULE[prime])
    return Fraction(10, 7)


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
def weight(modulus, adjusted=False):
    result = Fraction(1, modulus)
    for prime in prime_powers(modulus):
        result *= cap(prime, adjusted)
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


def maximum_mass(rows, adjusted=False):
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
                    allocated = min(remaining, count * cap(p, adjusted) / size)
                    bound += allocated * value
                    remaining -= allocated
                    if remaining == 0:
                        break
                next_values.append(bound)
            values = next_values
        best = max(best, values[-1])
    return best


def viable_pairs(target, limit, adjusted):
    # W(d) <= 2/sqrt(3d), and W(d) <= W(7) for non-special d.
    minimum = target - weight(7, adjusted)
    assert minimum > 0 and minimum**2 * limit > Fraction(4, 3)
    labels = [d for d in range(7, limit + 1, 2) if d % 5 and d not in SPECIAL
              and weight(d, adjusted) >= minimum]
    return [pair for pair in combinations(labels, 2)
            if sum(weight(d, adjusted) for d in pair) >= target]


def compatible_pairs(target, limit, adjusted):
    pairs = viable_pairs(target, limit, adjusted)
    survivors = []
    for i, left in enumerate(pairs):
        for right in pairs[i + 1:]:
            if set(left) & set(right):
                continue
            if sum(weight(lcm(a, b), adjusted) for a in left for b in right) < target:
                continue
            ceiling = maximum_mass((left, right), adjusted)
            if ceiling >= target:
                survivors.append((left, right))
            print(left, right, ceiling)
    return survivors


def compatible_with_nine():
    """The profile with one pure-5 row, three double rows and one triple."""
    pairs = viable_pairs(ADJUSTED_TARGET, ADJUSTED_LIMIT, True)
    remaining = []
    for partner in (7, 11, 13, 21):
        nine_row = (9, partner)
        for pair in pairs:
            if partner in pair:
                continue
            cross_cap = sum(weight(lcm(a, b), True) for a in pair for b in nine_row)
            if cross_cap < ADJUSTED_TARGET:
                continue
            ceiling = maximum_mass((pair, nine_row), True)
            if ceiling < ADJUSTED_TARGET:
                continue
            remaining.append((pair, partner))
            excluded = SPECIAL.union(pair, {partner})
            scores = []
            for d in range(7, 5001, 2):
                if d % 5 and d not in excluded:
                    cross = sum(weight(lcm(a, b, d), True) for a in pair for b in nine_row)
                    scores.append(min(weight(d, True), cross))
            tail = Fraction(1, 50)
            assert tail**2 * 5000 > Fraction(4, 3)
            upper = sum(sorted(scores + [tail] * 3, reverse=True)[:3])
            assert upper < ADJUSTED_TARGET
            print("Nine-row pairs", pair, nine_row, "triple upper", upper)
    assert remaining == [((21, 27), 7), ((7, 27), 21), ((7, 63), 21)]


def two_triples_under_three():
    """The profile with singleton cofactors 1 and 3 and a double using 9."""
    for partner in (7, 11, 13, 21, 27, 33, 39):
        scores = []
        for d in range(7, 10001, 2):
            if d % 5 and d not in SPECIAL and d != partner:
                scores.append(min(weight(lcm(3, d)),
                                  weight(lcm(9, d)) + weight(lcm(3, partner, d))))
        tail = Fraction(1, 50)
        assert tail**2 * 10000 > Fraction(4, 3)
        upper = sum(sorted(scores + [tail] * 6, reverse=True)[:6])
        assert upper < 2 * TARGET
        print("Two-triple upper for partner", partner, upper)


def check(adjusted):
    if adjusted:
        assert not compatible_pairs(ADJUSTED_TARGET, ADJUSTED_LIMIT, True)
        print("The adjusted measure excludes all pairs of nonspecial double rows.")
        compatible_with_nine()
        two_triples_under_three()
        return
    survivors = compatible_pairs(TARGET, LIMIT, False)
    assert survivors == [((7, 33), (11, 21))]
    core = (CORE[:2], CORE[2:])
    ninth = maximum_mass((*core, (9,)))
    assert ninth == Fraction(2320, 33957)
    # Any partner other than 1, 3, 7 and 9 has weight at most W(21).
    assert ninth + weight(21) < TARGET
    print("Only compatible pairs:", survivors[0])
    print("Upper bound inside any class modulo 9:", ninth)


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("--adjusted", action="store_true")
    check(parser.parse_args().adjusted)
