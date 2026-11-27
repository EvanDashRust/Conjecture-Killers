"""Distortion and dyadic prime-count certificate for arbitrarily many fresh coordinates."""
from argparse import ArgumentParser
from fractions import Fraction
from math import isqrt
from pathlib import Path

from fresh_coordinate_bound import bound
from prefix_sat import read

SCALE=10**14


def up(a,b):
    return -(-a//b)


def primes_to(limit):
    flags=bytearray([1])*(limit+1)
    flags[:2]=b"\0\0"
    for p in range(2,isqrt(limit)+1):
        if flags[p]:
            flags[p*p::p]=b"\0"*((limit-p*p)//p+1)
    return [i for i,v in enumerate(flags) if v]


def distortion(primes,cut,split,pair_bound,delta,small):
    gamma=1/(1-delta)
    charge=1/(4*delta*(1-delta))
    m=up(pair_bound.numerator*SCALE,pair_bound.denominator)
    # Small exceptional coordinates stay uniform. Pay their head-only classes separately.
    for p in small:
        r=p-1
        m+=up(m*(3*p-1),r*r)
    finite=0
    for p in primes:
        if p<cut or p in small:continue
        r=p-1
        finite+=up(m*charge.numerator,charge.denominator*r*r)
        m+=up(m*gamma.numerator*(3*p-1),gamma.denominator*r*r)
    # In each dyadic block [n,2n), n>=N=2^split, at most 2n/split primes.
    n=2**split
    b=gamma*(3+Fraction(2,n))*2/split
    mult=1/(1-b/8)**8
    assert 0<b<1 and mult<2
    tail=Fraction(m,SCALE)*charge*Fraction(2,split*n)*mult/(1-mult/2)
    return Fraction(finite,SCALE),tail


if __name__=="__main__":
    p=ArgumentParser()
    p.add_argument("--cut",type=int,default=1250)
    p.add_argument("--split",type=int,default=20)
    p.add_argument("--small",nargs="*",type=int,default=[])
    p.add_argument("--delta",default="1/4")
    args=p.parse_args()
    from math import prod
    from prefix_lift import is_prime
    assert 79<=args.cut<=2**args.split and len(set(args.small))==len(args.small)
    assert all(73<q<args.cut and is_prime(q) for q in args.small)
    root=Path(__file__).resolve().parent
    base=read(root/"prefix_candidate.json")
    cert=read(root/"Runs"/"product_mixture.json")
    t,_=bound(base,cert)
    u,_=bound(base,cert,pairs=True)
    finite,tail=distortion(primes_to(2**args.split),args.cut,args.split,u,Fraction(args.delta),args.small)
    head=t*(prod(Fraction(q,q-1) for q in args.small)-1)
    total=head+finite+tail
    print("pair upper",u,float(u))
    print("head, finite, tail:",float(head),float(finite),float(tail))
    print("total upper (ceiling / 10^12):",up(total.numerator*10**12,total.denominator))
    print("excluded" if total<1 else "inconclusive")
