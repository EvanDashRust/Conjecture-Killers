"""Exact variable-subset avoidance certificate on Harrington's seed-free CRT product."""
import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
from math import gcd, prod, isqrt
import json
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from harrington_seed import WITNESS, seed, meets_witness

UNIT = 10_000


@lru_cache(None)
def local_cap(prime, power):
    if prime not in WITNESS:
        return Fraction(1,power)
    period, values = WITNESS[prime]
    common = gcd(period,power)
    max_count = max(Counter(x%common for x in values).values())
    return Fraction(common*max_count,power*len(values))


def prove(moduli, primes):
    groups = defaultdict(Fraction)
    for modulus in moduli:
        residual = modulus
        weights = {}
        for i,p in enumerate(primes):
            power=1
            while residual%p==0:
                residual//=p
                power*=p
            mass=local_cap(p,power)
            if mass<1:
                weights[i]=mass
        assert residual==1
        support=sum(1<<i for i in weights)
        groups[support]+=prod(weights.values())
    if groups[0]:
        return None
    survival=[1-groups[1<<i] for i in range(len(primes))]
    if min(survival)<=0:
        return None
    # Condition away the one-coordinate events separately on each axis.
    by_pivot=[[] for _ in primes]
    for mask,mass in groups.items():
        if mask.bit_count()<2:
            continue
        conditioned=mass/prod(survival[i] for i in range(len(primes)) if mask>>i&1)
        scaled=conditioned*UNIT**mask.bit_count()
        upper=-(-scaled.numerator//scaled.denominator)
        by_pivot[(mask&-mask).bit_length()-1].append((mask,upper))
    z=[1]
    for remaining in range(1,1<<len(primes)):
        bit=remaining&-remaining
        amount=z[remaining^bit]*UNIT
        for support,upper in by_pivot[bit.bit_length()-1]:
            if support&remaining==support:
                amount-=upper*z[remaining^support]
        if amount<=0:
            return None
        z.append(amount)
    return Fraction(z[-1],UNIT**len(primes))*prod(survival)


def primes_to(n):
    return [p for p in range(3,n+1,2) if all(p%d for d in range(3,isqrt(p)+1,2))]


def peel(labels, primes):
    """Remove fresh coordinates in decreasing order; assign them in reverse order."""
    residual=set(labels)
    removed=[]
    for q in sorted(set(primes)-set(WITNESS),reverse=True):
        incident={m for m in residual if m%q==0}
        if not incident:
            continue
        load=Fraction(0)
        for m in incident:
            n=m
            while n%q==0:
                n//=q
            load+=Fraction(n,m)
        if load<1:
            residual-=incident
            removed.append((q,load))
    active=[p for p in primes if any(m%p==0 for m in residual)]
    return residual,active,removed


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--candidate",default=str(Path(__file__).with_name("harrington_reoptimized.json")))
    parser.add_argument("--move",type=int,nargs="*",default=[])
    parser.add_argument("--through",type=int,help="include every unused supported odd modulus up to the bound")
    args=parser.parse_args()
    result=json.loads(Path(args.candidate).read_text())
    frozen=dict(seed())
    assert all(not meets_witness(m,a) for m,a in frozen.items())
    assert set(args.move)<=frozen.keys()
    primes=result["primes"]
    labels=set(m for m,r in result["additions"])|set(args.move)
    if args.through:
        labels.update(m for m in range(3,args.through+1,2) if m not in frozen)
        primes=sorted(set(primes)|set(primes_to(args.through)))
    residual,active,peeled=peel(labels,primes)
    margin=prove(residual,active)
    print("variable labels",len(labels),"remaining seed",len(frozen)-len(args.move),
          "active primes",active,"residual labels",len(residual),"peeled primes",len(peeled))
    if margin is None:
        print("Inconclusive.")
    else:
        print("PROVED every phase assignment misses mass at least",margin,"on the residual prime coordinates before extension")
        print("lower bound to six decimal places:",(10**6*margin.numerator)//margin.denominator)


if __name__=="__main__":
    main()
