"""Certificate for conditional lower bounds on the number of 3-divisible moduli."""
from fractions import Fraction

from three_free_loss import prime_sieve, schedule

LIMIT = 100_000
TARGET = Fraction(7494, 10_000)
COUNTS = {
    (3,): 39,
    (9,): 19,
    (15,): 20,
    (3, 9): 53,
    (3, 15): 55,
    (9, 15): 27,
    (3, 9, 15): 76,
}


def weighted_moduli():
    caps = {p: 1 / (1 - delta) for p, delta in schedule(3).items()}
    default = Fraction(10, 7)
    assert all(cap**4 <= p for p, cap in caps.items())
    assert default**4 <= 5
    factors = [Fraction(1)] * (LIMIT + 1)
    prime = prime_sieve(LIMIT)
    for p in range(5, LIMIT + 1, 2):
        if prime[p]:
            for d in range(p, LIMIT + 1, 2 * p):
                factors[d] *= caps.get(p, default)
    ranked = []
    for m in range(3, LIMIT + 1, 6):
        d = m
        while d % 3 == 0:
            d //= 3
        weight = TARGET if d == 1 else factors[d] / d
        ranked.append((weight * d / m, m))
    return sorted(ranked, reverse=True)


def check():
    ranked = weighted_moduli()
    for excluded, minimum in COUNTS.items():
        available = [weight for weight, m in ranked if m not in excluded]
        last = available[minimum - 2]
        # Every unlisted modulus m has weight <= m^(-3/4).
        assert last**4 * LIMIT**3 > 1
        upper = sum(available[:minimum - 1])
        assert upper < TARGET
        scaled_upper = -(-upper.numerator * 10**9 // upper.denominator)
        print(excluded, minimum, scaled_upper)


if __name__ == "__main__":
    check()
