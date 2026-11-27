"""Upper bound on covered distortion mass for s-fold labels on primes >= P."""
import argparse
from fractions import Fraction as Q
from math import prod

SCALE = 10**18
PREFIX = 20_000
END = 10_000_000
GAMMA = Q(10, 7)
PUBLISHED_TAIL = Q(8082310506662, SCALE)


def ceiling(x):
    return -(-x.numerator // x.denominator)


def ceil_div(x, y):
    return -(-x // y)


def primes_through(n):
    from math import isqrt
    entries = bytearray(b"\x01") * (n + 1)
    for p in range(2, isqrt(n) + 1):
        if entries[p]:
            entries[p*p::p] = bytes((n-p*p)//p + 1)
    return (p for p in range(2, n+1) if entries[p])


def moment_factor(p):
    return 1 + GAMMA * Q(7*p*p - 2*p + 1, (p-1)**3)


def bound(min_prime, multiplicity):
    if not 7 <= min_prime <= PREFIX or multiplicity < 1:
        raise ValueError("Start between 7 and the prefix cap, with positive multiplicity")
    distribution = {1: SCALE}
    first = third = SCALE
    removed = 0
    ratio = Q(2, 31)  # omit Dai et al.'s initial third moment for D_3
    highest_threshold = 3*(PREFIX-1)//(10*multiplicity)
    for p in primes_through(END):
        if p < 7:
            continue
        if p < min_prime:
            ratio /= moment_factor(p)
            continue
        r = p - 1
        if p <= PREFIX:
            t = Q(3*r,10*multiplicity)
            correction = sum((t.numerator - n*t.denominator)*mass
                             for n,mass in distribution.items() if t.denominator*n<t.numerator)
            positive = Q(first*t.denominator - t.numerator*SCALE + correction, t.denominator)
            removed += ceiling(GAMMA*multiplicity*positive/r)
            probs = [0, ceiling((1-GAMMA/p)*SCALE)]
            probs.extend(ceiling(GAMMA*(1-Q(1,p))*SCALE/p**(d-1)) for d in range(2,10))
            probs.append(ceiling(GAMMA*SCALE/p**9))
            new = {}
            for n,mass in distribution.items():
                for d in range(1,min(10,highest_threshold//n)+1):
                    key = d*n
                    new[key] = new.get(key,0) + ceil_div(mass*probs[d], SCALE)
            distribution = new
            first = ceiling(first * (1 + GAMMA/r))
        else:
            removed += ceil_div(4000*third*multiplicity**3,1701*r**3)
        third += ceil_div(third*10*(7*p*p-2*p+1),7*r**3)
    return Q(removed,SCALE)+ratio*PUBLISHED_TAIL*multiplicity**3


if __name__ == "__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("minimum_prime",type=int)
    parser.add_argument("multiplicity",type=int)
    args=parser.parse_args()
    v=bound(args.minimum_prime,args.multiplicity)
    print("Total covered mass upper bound",v)
    print("Outward decimal numerator over 10^9",ceiling(v*10**9))
