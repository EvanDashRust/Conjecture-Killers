"""Exact checker for the mixed-fresh-prime exclusion around Harrington's seed."""
from argparse import ArgumentParser
from fractions import Fraction as Q
from math import prod
from pathlib import Path
import sys

parent = Path(__file__).resolve().parent.parent
checkpoint = parent if (parent / "harrington_seed.py").is_file() else parent / "selfridge3"
sys.path.insert(0, str(checkpoint))
from harrington_obstruction import (
    GROUP_SCALE, PRIMES, SCALE, ceil_ratio, condition_single_coordinates,
    old_groups, prime_sieve, scaled_ceil, shearer_survival,
)


def distribution_upper(alphabets, limit):
    mass = [0] * (limit + 1)
    mass[1] = SCALE
    for p, s in zip(PRIMES, alphabets):
        factor_bounds = [0, scaled_ceil(1 - 1/s)]
        probability = (1 - Q(1, p)) / s
        for e in range(2, limit + 1):
            upper = scaled_ceil(probability)
            if upper == 1:
                factor_bounds.extend([1] * (limit + 1 - e))
                break
            factor_bounds.append(upper)
            probability /= p
        updated = [0] * (limit + 1)
        for d, upper in enumerate(mass[1:], 1):
            if upper:
                for factor in range(1, limit // d + 1):
                    bound = factor_bounds[factor]
                    if bound:
                        updated[d*factor] += ceil_ratio(upper * bound, SCALE)
        mass = updated
    return mass


def optimal_stage(prefix, moment_prefix, scaled_mean, p, last):
    # Adjacent payoff ratios have the sign of
    # scaled_mean - (p-1)*SCALE + sum_{d <= t} (p-1-d)*upper[d].
    # This expression increases on the admissible interval.
    r = p-1
    lo, hi = 0, last
    while lo < hi:
        t = (lo+hi)//2
        diff = scaled_mean - r*SCALE + r*prefix[t] - moment_prefix[t]
        if diff >= 0:
            hi = t
        else:
            lo = t+1
    t=lo
    return ceil_ratio(scaled_mean - t*SCALE + t*prefix[t]-moment_prefix[t],r-t)


def verify(convex_last=40000, prime_last=600000, fixed=Q(1,6), count=5):
    weights = old_groups()
    alphabets = condition_single_coordinates(weights)
    # Match the group estimates in the earlier independently checked certificate.
    old = shearer_survival([Q(ceil_ratio(w.numerator*GROUP_SCALE,w.denominator),GROUP_SCALE)
                            for w in weights])
    m1 = scaled_ceil(prod(1 + Q(p,p-1)/s for p,s in zip(PRIMES,alphabets)))
    m2 = prod(1+Q(p*(3*p-1),(p-1)**2)/s for p,s in zip(PRIMES,alphabets))
    cap = distribution_upper(alphabets,convex_last)
    prefix, moment_prefix = [0],[0]
    for d,u in enumerate(cap[1:],1):
        prefix.append(prefix[-1]+u)
        moment_prefix.append(moment_prefix[-1]+d*u)
    sieve=prime_sieve(prime_last)
    small=0
    for p in range(19,convex_last+1):
        if sieve[p]:
            threshold=max(fixed,Q(count,p))
            allowed=(p-1)*(1-2*threshold)
            assert allowed>=0
            small+=optimal_stage(prefix,moment_prefix,m1,p,allowed.numerator//allowed.denominator)
    middle=sum(ceil_ratio(SCALE,(p-1)**2)
               for p in range(convex_last+1,prime_last+1) if sieve[p])
    # Tail contains only odd q. Its terms are bounded by the first term plus
    # the integral of decreasing 1/x^2 on the remaining even denominators.
    tail_start=prime_last if prime_last%2==0 else prime_last+1
    tail=Q(1,tail_start**2)+Q(1,2*tail_start)
    assert (1-max(fixed,Q(count,convex_last+1)))**2>=Q(1,2)
    fresh=Q(small,SCALE)+m2*(Q(middle,SCALE)+tail)
    for title,x in (("old survivor lower",old),("small scaled",small),("mid scaled",middle),
                    ("second moment",m2),("tail",tail),("fresh upper",fresh),("gap",old-fresh)):
        print(title,x if title in {"small scaled","mid scaled","second moment","tail"} else f"{float(x):.14f}",flush=True)
    assert fresh<old
    return small,middle,m2,tail


if __name__=="__main__":
    p=ArgumentParser()
    p.add_argument("--convex-last",type=int,default=40000)
    p.add_argument("--prime-last",type=int,default=600000)
    p.add_argument("--fixed",type=Q,default=Q(1,6))
    p.add_argument("--count",type=int,default=5)
    a=p.parse_args()
    verify(a.convex_last,a.prime_last,a.fixed,a.count)
