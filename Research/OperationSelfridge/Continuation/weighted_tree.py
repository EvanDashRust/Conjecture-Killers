"""Exact weighted prime-adic relaxation for lower bounds on class counts."""
from argparse import ArgumentParser
from fractions import Fraction as Q
from functools import lru_cache
from math import isqrt
from time import monotonic

from three_free_loss import schedule

SCALE = 10_000
DEFICITS = {3: 7494, 5: 2132}


def largest_weights(maximum, excluded, deficit):
    adjustments=schedule(excluded,True)

    def prime_factor(p):
        if p==3:
            return Q(2)
        return 1/(1-adjustments.get(p,Q(3,10)))

    def weight(d):
        n=d
        w=Q(1,d)
        for p in range(3,isqrt(d)+1,2):
            if n%p==0:
                w*=prime_factor(p)
                while n%p==0:
                    n//=p
            if n==1:
                break
        if n>1:
            w*=prime_factor(n)
        return w

    cutoff=12_000
    ranked=[(Q(deficit,SCALE),1)]
    ranked.extend((weight(d),d) for d in range(3,cutoff,2) if d%excluded)
    ranked.sort(reverse=True)
    top=ranked[:maximum]
    # Except for prime 3, every cap factor is below sqrt(p).
    # For p=3, the cap 2 contributes an extra factor 2/sqrt(3).
    assert top[-1][0]**2 * cutoff > Q(4,3)
    return tuple(-(-w.numerator*SCALE//w.denominator) for w,d in top),top


def compute(maximum, radix, deficit):
    weights, labels = largest_weights(maximum,radix,deficit)
    # Contributions at future depths 1..maximum, in units of radix^-maximum.
    pool=sorted((w*radix**(maximum-e) for e in range(1,maximum+1) for w in weights), reverse=True)
    capacity=[0]
    for w in pool[:maximum]:
        capacity.append(capacity[-1]+w)

    @lru_cache(None)
    def placements(open_nodes, n):
        states={open_nodes}
        for w in weights[:n]:
            reachable=set()
            for v in states:
                last=None
                for i,d in enumerate(v):
                    if d==last:
                        continue
                    last=d
                    dest=v[:i]+v[i+1:]
                    if d>w:
                        dest=tuple(sorted(dest+(d-w,),reverse=True))
                    reachable.add(dest)
                if not v:
                    reachable.add(v)
            states=reachable
        return states

    @lru_cache(None)
    def feasible(deficits, budget):
        if not deficits:
            return True
        if radix*len(deficits)>budget or sum(deficits)*radix**maximum>capacity[budget]:
            return False
        children=tuple(x for d in deficits for x in (d,)*radix)
        # An empty level can be collapsed by retaining an arbitrary child
        # for each active node and restricting all subsequent classes.
        for k in range(budget,0,-1):
            for v in placements(children,k):
                if feasible(v,budget-k):
                    return True
        return False

    for n in range(1,maximum+1):
        begun=monotonic()
        result=feasible((deficit,),n)
        print(n,result,round(monotonic()-begun,3),feasible.cache_info(),flush=True)
        if result:
            print("First feasible relaxed count:",n,flush=True)
            return n
    print("Excluded every count through",maximum,flush=True)
    return None


if __name__=="__main__":
    p=ArgumentParser()
    p.add_argument("--max",type=int)
    p.add_argument("--prime",type=int,choices=(3,5),default=3)
    a=p.parse_args()
    maximum=a.max if a.max is not None else {3:18,5:12}[a.prime]
    compute(maximum,a.prime,DEFICITS[a.prime])
