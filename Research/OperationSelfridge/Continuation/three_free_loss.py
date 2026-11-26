"""Directed-rounding distortion bounds when omitting moduli divisible by 3 or 5."""
from argparse import ArgumentParser
from fractions import Fraction as Q
from math import isqrt, prod

SCALE = 10**18
PREFIX_LAST = 20_000
PRIME_LAST = 10_000_000
MULTIPLIER_CAP = 10
PREPRINT_BEYOND = Q(8082310506662, SCALE)


def prime_sieve(limit):
    sieve = bytearray(b"\1") * (limit + 1)
    sieve[:2] = b"\0\0"
    for p in range(2,isqrt(limit)+1):
        if sieve[p]:
            sieve[p*p::p] = bytes((limit-p*p)//p+1)
    return sieve


def up(x):
    return -(-x.numerator // x.denominator)


def ratio_up(numerator, denominator):
    return -(-numerator // denominator)


def prefix_and_middle(prefix_limit, adjustments, excluded):
    middle = 0
    prefix = 0
    distribution = {1: SCALE}
    first = third = SCALE
    histogram_limit = max(
        [3 * prefix_limit // 10]
        + [int(delta * (p - 1)) for p, delta in adjustments.items()]
    )
    if excluded==5:
        first=2*SCALE
        third=31*SCALE//2
        distribution={1:ratio_up(SCALE,3),**{
            d:ratio_up(4*SCALE,3**d) for d in range(2,MULTIPLIER_CAP)
        },MULTIPLIER_CAP:ratio_up(2*SCALE,3**(MULTIPLIER_CAP-1))}
    prime = prime_sieve(PRIME_LAST)
    for p in range(5, PRIME_LAST + 1, 2):
        if p==excluded or not prime[p]:
            continue
        delta=adjustments.get(p,Q(3,10))
        c=1/(1-delta)
        r=p-1
        if p<=prefix_limit:
            threshold = delta*r
            # Replace each factor by min(D_p,10) only in E[(threshold-D)_+].
            # The true first moment is propagated without truncation.
            correction=0
            a,b=threshold.numerator,threshold.denominator
            for d, scaled_probability in distribution.items():
                if b*d<a:
                    correction+=(a-b*d)*scaled_probability
            positive_part=Q(b*first-a*SCALE+correction,b)
            prefix+=up(c*positive_part/r)
            odds=[0,up((1-c/p)*SCALE)]
            mass=c*(1-Q(1,p))/p
            for j in range(2,MULTIPLIER_CAP):
                odds.append(up(mass*SCALE))
                mass/=p
            odds.append(up(c*SCALE/p**(MULTIPLIER_CAP-1)))
            next_mass={}
            for d,prob in distribution.items():
                for j in range(1,min(MULTIPLIER_CAP,histogram_limit//d)+1):
                    n=d*j
                    next_mass[n]=next_mass.get(n,0)+ratio_up(prob*odds[j],SCALE)
            distribution=next_mass
            first=up(Q(first)*(1+c/r))
        else:
            middle+=ratio_up(4000*third,1701*r**3)
        # Only integer updates for the long third-moment tail.
        third+=ratio_up(third*c.numerator*(7*p*p-2*p+1),c.denominator*r**3)
    return Q(prefix,SCALE),Q(middle,SCALE)


def schedule(excluded, optimized=True):
    # At p=5 each fibre load is at most 1/4, so delta=1/4 costs zero.
    numerator_schedule = (
        {7:2, 11:2, 13:4, 17:4, 19:4, 23:6, 29:8, 31:8,
         37:8, 41:12, 43:12, 47:12, 53:16, 59:16, 61:16, 67:16, 71:16}
        if excluded==3 else
        {7:2, 11:2, 13:3, 17:4, 19:4, 23:6, 29:6, 31:8, 37:8, 41:8}
    )
    adjustments={p:Q(a,p-1) for p,a in numerator_schedule.items()} if optimized else {}
    if excluded==3:
        adjustments[5]=Q(1,4)
    return adjustments


def bound(prefix_limit=PREFIX_LAST, excluded=3, optimized=True):
    adjustments=schedule(excluded,optimized)
    assert 100<=prefix_limit<=PRIME_LAST
    first,middle=prefix_and_middle(prefix_limit,adjustments,excluded)
    def moment(p,delta):
        return 1+Q(7*p*p-2*p+1,(p-1)**3)/(1-delta)
    # At p > 10^7, the cubic stage bound is linear in the third moment.
    # Compare the explicit initial-and-adjusted third-moment factors with §4.3.
    scaling=moment(5,Q(1,4))/Q(31,2) if excluded==3 else Q(1)
    scaling*=prod(moment(p,d)/moment(p,Q(3,10)) for p,d in adjustments.items() if p!=5)
    beyond=PREPRINT_BEYOND*scaling
    total=first+middle+beyond
    print("prefix:",first,float(first),flush=True)
    print("middle:",middle,float(middle),flush=True)
    print("beyond:",beyond,float(beyond),flush=True)
    print("guaranteed uncovered:",1-total,float(1-total),flush=True)
    return 1-total


if __name__=="__main__":
    p=ArgumentParser()
    p.add_argument("--prefix",type=int,default=PREFIX_LAST)
    p.add_argument("--excluded",type=int,choices=(3,5),default=3)
    p.add_argument("--baseline",action="store_true")
    args=p.parse_args()
    uncovered = bound(args.prefix,args.excluded,not args.baseline)
    if args.prefix == PREFIX_LAST:
        if args.excluded == 3 and not args.baseline:
            assert uncovered > Q(7494, 10_000)
        if args.excluded == 5 and args.baseline:
            assert uncovered > Q(2097, 10_000)
