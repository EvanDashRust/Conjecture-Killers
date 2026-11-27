"""Rank restored-class caps to certify multiplicities after the cross_heights.py deletions."""
from fractions import Fraction as Q
from pathlib import Path
from cross_heights import CASES, MISSING_FIFTEEN, SCHEDULE, primes_through

LIMIT=400_000
# Lower margins rounded down, valid at both endpoints (cross_results.txt).
MARGINS={
    "both": (Q(24234,100000),Q(15345,100000)),
    "high3": (Q(9313,100000),Q(425,100000)),
    "high5": (Q(9136,100000),Q(247,100000)),
    "next": (Q(2550,100000),Q(0)),
}

def ranked(h3,h5,schedule):
    primes=primes_through(LIMIT)
    gs={}
    for p in primes:
        if p in (2,7):
            continue
        g=Q(2) if p==3 else Q(4,3) if p==5 else 1/(1-(Q(schedule[p],p-1) if p in schedule else Q(3,10)))
        assert g**4 <= p*(Q(16,3) if p==3 else 1)
        gs[p]=g
    # Retain rough parts coprime to 2,3,5,7, with a cutoff on the whole modulus.
    min_smooth=min(v for v in (3**(h3+1) if h3 else LIMIT,5**(h5+1) if h5 else LIMIT))
    max_rough=LIMIT//min_smooth
    weights=[Q(1)]*(max_rough+1)
    for p,g in gs.items():
        if p>max_rough:
            break
        if p>=11:
            for b in range(p,max_rough+1,p):
                weights[b]*=g
    candidates=[]
    from math import gcd
    A=1
    while 11*A<=LIMIT:
        B=1
        while 11*A*B<=LIMIT:
            if (h3 is not None and A>3**h3) or (h5 is not None and B>5**h5):
                factor=(gs[3] if A>1 else 1)*(gs[5] if B>1 else 1)
                for d in range(11,LIMIT//(A*B)+1,2):
                    if gcd(d,105)==1:
                        m=A*B*d
                        candidates.append((factor*weights[d]/m,m))
            B*=5
        A*=3
    return sorted(candidates,reverse=True)

if __name__=='__main__':
    for case,(h3,h5) in CASES.items():
        recorded = Path(__file__).with_name("cross_results.txt").read_text().splitlines()
        endpoints = [line.split() for line in recorded if line.startswith(case+" ")]
        assert {words[1] for words in endpoints}=={"t=5/9","t=2/3"}
        for words in endpoints:
            for pos,margin in zip((2,4), MARGINS[case]):
                assert not margin or Q(words[pos].split("=")[1]) > margin
        candidates=ranked(h3,h5,SCHEDULE if case=='high5' else MISSING_FIFTEEN)
        for orbit, margin in enumerate(MARGINS[case],1):
            if not margin:
                continue
            total=Q(0)
            for i,(w,m) in enumerate(candidates,1):
                if total+w>=margin:
                    # Any competitor of modulus > LIMIT is strictly lighter than w.
                    assert w**4*LIMIT**3 > Q(16,3)
                    print(f"{case} r={orbit} margin={margin} required={i} preceding_sum={total} ({float(total):.12f})",flush=True)
                    break
                total+=w
            else:
                raise AssertionError("insufficient search range")
