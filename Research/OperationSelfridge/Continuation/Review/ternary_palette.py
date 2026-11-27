"""Independent computation of the first 18 upper weights in the ternary audit."""
from fractions import Fraction as Q
from math import prod

CUTOFF = 4096
SCALE = 10000
EARLY = {5:1,7:2,11:2,13:4,17:4,19:4,23:6,29:8,31:8,37:8,41:12,
         43:12,47:12,53:16,59:16,61:16,67:16,71:16}


def cap(p):
    return Q(p-1,p-1-EARLY[p]) if p in EARLY else Q(10,7)


def weight(d):
    v = d
    factors = []
    divisor = 3
    while divisor * divisor <= v:
        if v % divisor == 0:
            factors.append(divisor)
        while v % divisor == 0:
            v //= divisor
        divisor += 2
    if v != 1:
        factors.append(v)
    return prod(map(cap, factors), start=Q(1)) / d


if __name__ == '__main__':
    assert all(cap(p)**2 <= p for p in EARLY) and Q(10,7)**2 < 5
    weights = [Q(7494,SCALE)] + [weight(d) for d in range(5,CUTOFF,2) if d%3]
    top = sorted(weights,reverse=True)[:18]
    assert top[-1]**2 * CUTOFF > 1
    print(*[-(-v.numerator*SCALE//v.denominator) for v in top])
