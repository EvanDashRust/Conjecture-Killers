"""Exact no-7 certificates for valuation caps and omitted primes."""
from argparse import ArgumentParser
from fractions import Fraction as Q
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "Review"))
from third_prime import MISSING_FIFTEEN
from joint_fibres import LIMIT, CAP, UNIT, ceiling, moments, check_loss, primes_through


def reciprocal_sum(p, height):
    if height is None:
        return Q(1, p-1)
    return (1 - Q(1, p**height)) / (p-1)


def coordinate(p, height, first):
    """Bounded histogram for the correction and uncapped moments."""
    gamma = 1 / (1-reciprocal_sum(p, height))

    def survival(e):
        if e == 0:
            return Q(1)
        if height is not None and e > height:
            return Q(0)
        return first if e == 1 else gamma / p**e

    probs = [survival(e)-survival(e+1) for e in range(CAP-1)] + [survival(CAP-1)]
    if height is None:
        a, b, c = moments(p, gamma)
        # Alter only P(T>=1). For f(T)=(1+T)^k the difference
        # between f(1) and f(0) is 2^k-1.
        correction = first - gamma/p
        mean = 1 + a + correction
        cube = 1 + 3*a + 3*b + c + 7*correction
    else:
        mean = 1 + sum(survival(e) for e in range(1, height+1))
        cube = 1 + sum(((e+1)**3-e**3)*survival(e) for e in range(1, height+1))
    assert all(q >= 0 for q in probs) and sum(probs) == 1
    return probs, mean, cube


def product_initial(a, b, z, w):
    d3, mean3, cube3 = coordinate(3, a, z)
    d5, mean5, cube5 = coordinate(5, b, w)
    hist = {}
    for i, u in enumerate(d3, start=1):
        for j, v in enumerate(d5, start=1):
            hist[i*j] = hist.get(i*j, 0) + ceiling(UNIT*u*v)
    return hist, ceiling(UNIT*mean3*mean5), ceiling(UNIT*cube3*cube5)


# A and B are inclusive valuation upper bounds; None means unbounded.
# An interval of z values needs both endpoints. The unrounded comparison
# is affine in z; outward rounding is done only after fixing each endpoint.
CASES = {
    "v3-le-2": (2, None, None, False, Q(129, 1000)),
    "v5-le-1": (None, 1, None, False, Q(101, 1000)),
    "v3-le-3-v5-le-2": (3, 2, None, False, Q(64, 10000)),
    "r1-v3-le-3": (3, None, None, True, Q(20, 1000)),
    "r1-v3-le-4-v5-le-2": (4, 2, None, True, Q(15, 1000)),
    "r1-without-23": (None, None, 23, True, Q(52, 1000)),
    "r1-without-29": (None, None, 29, True, Q(15, 1000)),
    "r1-without-31": (None, None, 31, True, Q(7, 1000)),
}


def run(case, endpoint, primes):
    a, b, omitted, phase_sensitive, claimed = CASES[case]
    u, v = reciprocal_sum(3, a), reciprocal_sum(5, b)
    g3, g5 = 1/(1-u), 1/(1-v)
    w = g5/5
    if phase_sensitive:
        # After avoiding the pure 3-classes, the larger root is 2.
        # Its mass z is minimized by removing exactly 1/9 from root 1
        # and the balance of the pure budget from root 2. It is at most g3/3.
        zmin = (Q(7,9)-u)*g3
        z = zmin if endpoint == "lo" else g3/3
        charge = g5*(g3*(u-Q(1,3))*v + (1-z)/5 + z*(v-Q(1,5)))
    else:
        z = g3/3
        charge = g3*g5*u*v
    prefix, middle, tail = check_loss(
        primes, g3, g5, lambda *_: product_initial(a, b, z, w),
        minimum_prime=11, schedule=MISSING_FIFTEEN,
        omit_stages=(() if omitted is None else (omitted,)),
    )
    survivor = 1-charge-prefix-middle-tail
    decimal_floor = (survivor * 10**9).__floor__()
    assert Q(decimal_floor, 10**9) < survivor
    print(case, endpoint, 'z', z, 'head', charge, 'prefix', prefix, 'middle', middle,
          'tail', tail, 'surviving>', decimal_floor, '/ 10^9', flush=True)
    assert survivor > claimed, (survivor, claimed)


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("case", nargs="?", choices=sorted(CASES))
    parser.add_argument("--endpoint", choices=("lo", "hi"))
    args = parser.parse_args()
    primes = primes_through(LIMIT)
    for case in ([args.case] if args.case else CASES):
        for endpoint in ([args.endpoint] if args.endpoint else
                         (["lo", "hi"] if CASES[case][3] else ["hi"])):
            run(case, endpoint, primes)
