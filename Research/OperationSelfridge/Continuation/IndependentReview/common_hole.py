"""Exact restoration counts from previously certified omitted-prime measures."""
from fractions import Fraction as F
from functools import cache
from math import gcd, lcm, prod
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "Review"))
from third_prime import EARLY, MISSING_FIFTEEN
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "TheoryJoint"))
from orbit_quantile import THRESHOLDS

MARGINS = {7: 181617, 11: 181617, 13: 119046, 17: 32890, 19: 6492, 23: 1000}
# (p, D): threshold label k=m/p, disjoint pairs of first-power cofactors.
PAIRS = {
    (7, 1): (57, [(9, 5), (3, 17), (15, 13)]),
    (11, 1): (73, [(9, 5), (3, 17), (15, 13)]),
    (13, 1): (61, [(15, 11), (9, 17), (5, 33), (3, 23), (27, 19)]),
    (17, 9): (333, [(45, 99), (27, 39), (15, 33), (5, 11),
                    (81, 13), (117, 135)]),
    (17, 15): (29, [(75, 9), (45, 25), (165, 195), (33, 13),
                    (11, 135), (55, 65), (27, 39)]),
    (19, 165): (363, [(495, 25), (99, 825), (45, 75), (9, 275)]),
    (23, 495): (81, [(297, 75), (1485, 25), (135, 2475), (27, 275)]),
    (23, 585): (81, [(1755, 75), (135, 25), (27, 2925), (351, 325)]),
}
LIMIT = 100_000
K_COUNTS = {7: 13, 11: 38, 13: 30, 17: 31, 19: 31, 23: 36}


@cache
def factors(n):
    f = []
    q = 3
    while q*q <= n:
        a = 0
        while n % q == 0:
            n //= q
            a += 1
        if a:
            f.append((q, a))
        q += 2
    if n > 1:
        f.append((n, 1))
    return f


def certificate(p):
    h, k = F(MARGINS[p], 10**6), K_COUNTS[p]
    schedule = EARLY if p in (7,11) else MISSING_FIFTEEN
    excluded = 11 if p == 7 else 7
    fourth_factor = F(1) if p == 23 else F(16, 3)
    def rough_gamma(q, table):
        return 1/(1-F(table[q], q-1)) if q in table else F(10, 7)
    def gamma(q):
        if p == 23:
            if q in (3, 5):
                return F(1)
            return max(rough_gamma(q, MISSING_FIFTEEN), rough_gamma(q, THRESHOLDS))
        if q == 3:
            return F(2)
        if q == 5:
            return F(4, 3)
        return rough_gamma(q, schedule)
    # For unspecified q >= 11 the constant cap satisfies gamma^4 <= 11.
    assert F(10, 7)**4 <= 11
    for q in {3, 5, *schedule, *THRESHOLDS} - {2, excluded, p}:
        assert gamma(q)**4 <= q * (fourth_factor if q == 3 else 1)
    @cache
    def weight(d):
        return prod((gamma(q) for q, _ in factors(d)), start=F(1)) / d

    # k < 2p guarantees singleton roots whose common cofactor period is D.
    # For k >= 2p, D=1 imposes no condition.
    if p in (17, 19, 23):
        bound = 1
        while h**4 * bound**3 <= fourth_factor:
            bound *= 2
        periods = [d for d in range(1, bound+1, 2) if d % excluded and d % p
                   and weight(d) >= h and prod(a+1 for _, a in factors(d)) >= 2*p-k]
    else:
        periods = [1]

    # Normalized projection mass at any cofactor outside the enumeration is < 1/20.
    large_cap = F(1, 5) if p == 23 else F(1, 20)
    assert LIMIT**3 * (h*large_cap)**4 > fourth_factor
    def estimate(D):
        G = weight(D)
        def w(d):
            # W(lcm(D,d)) = W(D)W(d)/W(gcd(D,d)).
            return min(F(1), G*weight(d)/(weight(gcd(d, D))*h))
        def u(b):
            d = b
            while d % p == 0:
                d //= p
            return w(d)*F(d, b)
        # Only labels exceeding the tail cap can affect these estimates.
        small = {b: u(b) for b in range(1, LIMIT, 2) if b % excluded}
        if (p, D) not in PAIRS:
            return sum(sorted([large_cap]*k + list(small.values()), reverse=True)[:k])
        anchor, pairs = PAIRS[p, D]
        rate = small[anchor]
        assert rate >= large_cap
        total = k*rate + sum(v-rate for v in small.values() if v > rate)
        used = set()
        for a,b in pairs:
            assert a != b and not (used & {a,b}) and a % p and b % p
            used.update((a,b))
            reduction = min(small[a]-rate, small[b]-rate, small[a]+small[b]-1-w(lcm(a,b)))
            assert reduction >= 0
            total -= reduction
        return total
    assert periods
    cases = [(estimate(D), D) for D in periods]
    worst, D = max(cases)
    assert worst < p
    print(f"p={p}, assume at most {k}, {len(periods)} period cases, worst D={D}")
    print(f"normalized sum <= {worst} < {p} (approx. {float(worst):.9f})")


if __name__ == "__main__":
    for prime in MARGINS:
        certificate(prime)
    for p, h, max_tau in [(23, F(52,1000), 6), (29,F(15,1000),8), (31,F(7,1000),9)]:
        bound=1
        while h**4*bound**3 <= F(16,3):
            bound *= 2
        def cap(q):
            if q in (3,5):
                return F(2) if q==3 else F(4,3)
            return 1/(1-F(MISSING_FIFTEEN[q],q-1)) if q in MISSING_FIFTEEN else F(10,7)
        admissible=[(prod(a+1 for _,a in factors(d)),d) for d in range(1,bound+1,2)
                    if d % p and d % 7 and prod((cap(q) for q,_ in factors(d)),start=F(1)) >= d*h]
        assert max(admissible)[0]==max_tau
        print(f"r=1 p={p} max singleton cofactors {max_tau}, N(p)>={2*p-max_tau}")
