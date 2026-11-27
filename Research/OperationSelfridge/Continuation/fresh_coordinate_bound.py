"""Rational mixture of empty products obstructing arbitrary new prefix coordinates."""
from collections import defaultdict
from fractions import Fraction
from itertools import product
from math import prod
from pathlib import Path
from argparse import ArgumentParser
from prefix_box import make_box,value
from prefix_sat import read
from empty_product import verify


def bound(base,cert,pairs=False):
    ps,hs=base["primes"],base["heights"]
    alph,_=make_box(ps,hs)
    boxes=[[int(a,16) for a in mask] for mask in cert["boxes"]]
    for box in boxes:
        verify(base,box)
    pts=[(w,Fraction(n,d)) for w,n,d in cert["head_weights"]]
    head=len(pts[0][0])
    assert all(h==0 for h in hs[head:])
    assert all(m>0 and len(w)==head and any(all(B[i]>>k&1 for i,k in enumerate(w))
               for B in boxes) for w,m in pts)
    total=sum(m for w,m in pts)
    head_sum=0
    single=Fraction(0)
    for modes in product(*(range(h+2) for h in hs[:head])):
        weights=defaultdict(Fraction)
        for w,m in pts:
            phase=tuple(value(ps[i],hs[i],alph[i][w[i]],e) for i,e in enumerate(modes) if e)
            weights[phase]+=m
        capacity=max(weights.values())/total
        head_sum+=capacity*(prod(2*e+1 for e in modes) if pairs else 1)
        if sum(e>0 for e in modes)==1:
            single=max(single,capacity)
    # All tail heights are zero. Each constrained coordinate fixes a single atom.
    denominators=[]
    for box in boxes:
        terms=[1]
        for mask in box[head:]:
            terms += [d*mask.bit_count() for d in terms]
        denominators.append(terms)
    from collections import Counter
    multiplicities=Counter()
    for mask,values in enumerate(zip(*denominators)):
        multiplicities[min(values)]+=3**mask.bit_count() if pairs else 1
    tail_sum=sum(Fraction(count,d) for d,count in multiplicities.items())
    single=max([single]+[Fraction(1,mask.bit_count()) for box in boxes for mask in box[head:]])
    return head_sum*tail_sum,single


if __name__=="__main__":
    p=ArgumentParser()
    p.add_argument("--candidate",default=str(Path(__file__).with_name("prefix_candidate.json")))
    p.add_argument("--certificate",default=str(Path(__file__).with_name("Runs")/"product_mixture.json"))
    a=p.parse_args()
    t,single=bound(read(a.candidate),read(a.certificate))
    print("old-mode sum upper",t,float(t))
    print("one moved old slot and one new prime, upper",single+t/78,float(single+t/78))
    for fresh in ([79],[79,83],[79,83,89],[79,83,89,97]):
        v=t*(prod(Fraction(q,q-1) for q in fresh)-1)
        print(fresh,float(v),"excluded" if v<1 else "inconclusive")
