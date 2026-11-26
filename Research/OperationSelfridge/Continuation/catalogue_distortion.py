"""Finite-catalogue phase exclusion by conditional distortion and scalar comparison."""
import argparse
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from math import lcm, prod
from pathlib import Path
import json

# Place alongside catalogue_obstruction.py (or set PYTHONPATH to its directory).
from catalogue_obstruction import local_cap, peel, primes_to
from harrington_seed import seed, meets_witness


def restrictions(m, primes):
    powers = {}
    for p in primes:
        f = 1
        while m % p == 0:
            m //= p
            f *= p
        if local_cap(p, f) < 1:
            powers[p] = f
    assert m == 1
    return powers


def integer_vector(values):
    den = lcm(*(v.denominator for v in values))
    return [v.numerator*(den//v.denominator) for v in values], den


def stage_loss(p, terms, prev, caps, deltas):
    if not terms:
        return Fraction(0)
    state = {(1 << len(terms))-1: 1}
    den = 1
    for q in prev:
        powers = sorted({d[q] for d in terms if q in d})
        if not powers:
            continue
        tails = [Fraction(1)] + [min(1, caps(q, f) / (1-deltas[q])) for f in powers] + [0]
        odds, step = integer_vector([a-b for a,b in zip(tails,tails[1:])])
        following = defaultdict(int)
        for power, coeff in zip([0]+powers, odds):
            if not coeff:
                continue
            mask = sum(1 << j for j,d in enumerate(terms) if d.get(q,0)<=power)
            for alive, mass in state.items():
                following[alive & mask] += mass * coeff
        state = following
        den *= step
    assert sum(state.values()) == den
    values, weights_den = integer_vector([caps(p, d[p]) for d in terms] + [deltas[p]])
    threshold = values.pop()
    @lru_cache(None)
    def load(mask):
        if not mask:
            return 0
        bit = mask & -mask
        return values[bit.bit_length()-1] + load(mask ^ bit)
    excess = sum(max(load(mask)-threshold,0)*mass for mask,mass in state.items())
    return Fraction(excess, den * weights_den) / (1-deltas[p])


def second_moment(p, terms, caps, deltas):
    # With delta=1/2, 2(x-1/2)_+ <= x^2. Comonotone
    # thresholds on each preceding coordinate give the joint inclusion mass.
    total = Fraction(0)
    for i, first in enumerate(terms):
        for j in range(i+1):
            second = terms[j]
            probability = Fraction(1)
            for q in (first.keys() | second.keys()) - {p}:
                f = max(first.get(q,1),second.get(q,1))
                probability *= min(1, caps(q,f)/(1-deltas[q]))
            total += (1 if i==j else 2)*caps(p,first[p])*caps(p,second[p])*probability
    mean = sum(caps(p, d[p])*prod(
        min(1, caps(q,f)/(1-deltas[q])) for q,f in d.items() if q!=p)
        for d in terms)
    variance = total - mean**2
    assert variance >= 0
    # For a<delta, (s-delta)_+ <= (s-a)^2 / (4*(delta-a)).
    # Evaluate several exact tangent quadratic majorants.
    delta = deltas[p]
    choices = [Fraction(0), mean]
    if mean < delta:
        choices += [mean - variance/(2*(delta-mean))]
    return min((variance+(mean-a)**2)/(4*(delta-a)*(1-delta))
               for a in choices if a < delta)


def prove(labels, primes, moment_from, tuned):
    residual, active, peeled = peel(labels,primes)
    families = [restrictions(m,active) for m in sorted(residual)]
    if any(not d for d in families):
        raise ValueError("Unrestricted event on this product domain")
    survival = {p: 1-sum((local_cap(p,d[p]) for d in families if list(d)==[p]),Fraction(0))
                for p in active}
    if min(survival.values(), default=1)<=0:
        raise ValueError("Unary bound inconclusive")
    @lru_cache(None)
    def caps(p, f):
        return min(Fraction(1), local_cap(p,f)/survival[p])
    nonsingle = [d for d in families if len(d)>1]
    stage = {p:[d for d in nonsingle if max(d)==p] for p in active}
    deltas = {p:Fraction(1,2) if stage[p] else Fraction(0) for p in active}
    if tuned:
        for p, delta in ((11,Fraction(7,25)),(13,Fraction(43,100))):
            if stage.get(p):
                deltas[p] = delta
    loss = 0
    for i,p in enumerate(active):
        if p >= moment_from and stage[p]:
            amount = second_moment(p, stage[p], caps, deltas)
        else:
            amount = stage_loss(p, stage[p], active[:i], caps, deltas)
        loss += amount
        print("stage",p,"terms",len(stage[p]),"upper (millionths)",-(-amount.numerator*10**6//amount.denominator))
    print("Peeled",len(peeled),"active",len(active),"residual labels",len(residual))
    print("outward loss upper, denominator 1e12:", -(-loss.numerator*10**12//loss.denominator))
    return loss


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument("candidate",type=Path)
    parser.add_argument("--through",type=int,default=6000)
    parser.add_argument("--move",type=int,nargs="*",default=[9,25])
    parser.add_argument("--moment-from",type=int,default=48)
    parser.add_argument("--tuned",action="store_true")
    args=parser.parse_args()
    result=json.loads(args.candidate.read_text())
    frozen=dict(seed())
    assert set(args.move)<=frozen.keys()
    assert all(not meets_witness(m,r) for m,r in frozen.items())
    labels={m for m,_ in result["additions"]}|set(args.move)
    labels.update(m for m in range(3,args.through+1,2) if m not in frozen)
    primes=sorted(set(result["primes"])|set(primes_to(args.through)))
    loss=prove(labels,primes,args.moment_from,args.tuned)
    print("PROVED" if loss<1 else "Inconclusive")
    if args.through==6000 and set(args.move)=={9,25} and args.moment_from>=48:
        assert loss < Fraction(614,1000)
