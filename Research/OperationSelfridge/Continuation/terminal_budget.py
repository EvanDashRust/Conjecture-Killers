"""Exact upper volume for independent rectangular terminals; lower volume of base holes."""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import prod
from pathlib import Path
import json

from prefix_box import make_box,value


def assigned_mass(primes,heights,alphabet):
    return [{e:Counter(value(p,h,a,e) for a in A)
             for e in range(1,h+2)} for p,h,A in zip(primes,heights,alphabet)]


def upper(primes,heights,alphabet,tables):
    states={1:Fraction(1)}
    for h,A,table in zip(heights,alphabet,tables):
        options=[(1,Fraction(1))]
        options.extend((e+1,Fraction(max(table[e].values()),len(A))) for e in range(1,h+2))
        new={}
        for k,weight in states.items():
            for capacity,mass in options:
                size=k*capacity
                new[size]=max(new.get(size,0),weight*mass)
        states=new
    limit=max(states)
    rough=bytearray(b'\1')*(limit+1)
    for p in [2]+primes:
        rough[::p]=bytes(limit//p+1)
    rough[:3]=bytes(3)
    threshold=[]
    best=Fraction(0)
    for k in sorted(states,reverse=True):
        best=max(best,states[k])
        threshold.append((k,best))
    low=0
    total=Fraction(0)
    for k,mass in reversed(threshold):
        total+=rough.count(1,low+1,k+1)*mass
        low=k
    return total


def lower(primes,heights,alphabet,tables,patterns,head):
    # Condition on the first axes, then eliminate every remaining unary cylinder
    # exactly before bounding the multivariate remainder by a union bound.
    from collections import defaultdict
    full=[(1<<len(A))-1 for A in alphabet]
    masks={(i,e,v):sum(1<<j for j,x in enumerate(alphabet[i])
                       if value(primes[i],heights[i],x,e)==v)
           for pat in patterns for i,e,v in pat}
    groups=defaultdict(list)
    for pat in patterns:
        restriction=tuple(t for t in pat if t[0]<head)
        groups[restriction].append([(i,masks[i,e,v]) for i,e,v in pat if i>=head])
    safe=0
    for roots in product(*(range(len(A)) for A in alphabet[:head])):
        compatible=[tail for fixed,items in groups.items()
                    if all(masks[i,e,v]>>roots[i]&1 for i,e,v in fixed) for tail in items]
        if [] in compatible:
            continue
        domain=full[:]
        for tail in compatible:
            if len(tail)==1:
                i,m=tail[0]
                domain[i]&=~m
        sizes=[m.bit_count() for m in domain]
        volume=prod(sizes[head:])
        if not volume:
            continue
        loss=0
        for tail in compatible:
            if len(tail)==1:
                continue
            hits=volume
            for i,m in tail:
                hits=hits//sizes[i]*(m&domain[i]).bit_count()
            loss+=hits
            if loss>=volume:
                break
        safe+=max(0,volume-loss)
    return Fraction(safe,prod(map(len,alphabet)))


def main():
    p=ArgumentParser()
    p.add_argument("candidate",nargs="?",default=str(Path(__file__).with_name("prefix_candidate.json")))
    p.add_argument("--head",type=int,default=3)
    a=p.parse_args()
    data=json.loads(Path(a.candidate).read_text())
    ps,hs=data["primes"],data["heights"]
    alph,pure=make_box(ps,hs)
    assert json.loads(json.dumps(pure))==data["pure"] and not data.get("terminal")
    tables=assigned_mass(ps,hs,alph)
    patches=upper(ps,hs,alph,tables)
    holes=lower(ps,hs,alph,tables,[tuple(map(tuple,p)) for p in data["patterns"]],a.head)
    print("All rough terminal rectangles together occupy at most",patches,float(patches))
    print("Base hole measure at least",holes,float(holes))
    print("Proved exclusion:",holes>patches)
if __name__=="__main__":
    main()
