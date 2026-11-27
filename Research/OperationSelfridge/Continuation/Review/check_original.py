"""Independent integer checks of the original per-root auxiliary construction."""
from functools import lru_cache
from itertools import product
import importlib.util
import json
from math import gcd
from pathlib import Path
import sys

from shared_lift import crt, prime

def canonical_schematic(primes,heights,patterns):
    lookup={}
    q=max([2,*primes,*(1+h for h in heights)])+1
    for i,(p,h) in enumerate(zip(primes,heights)):
        for root in range(p**h):
            while not prime(q):
                q+=1
            lookup[i,root]=q
            q+=1
    return lookup

def concrete_hole(data):
    if data.get("terminal"):
        raise ValueError("A terminal requires a separate auxiliary check")
    primes,heights=data["primes"],data["heights"]
    patterns=data["pure"]+data["patterns"]
    lookup=canonical_schematic(primes,heights,patterns)
    word=data["uncovered_atom_word"]
    equations=[(p**(h+1),r+d*p**h) for p,h,(r,d) in zip(primes,heights,word)]
    equations.extend((q,q-1) for q in lookup.values())
    _,x=crt(equations)
    # Test the only possible local auxiliary branch at each auxiliary prime.
    for (i,r),q in lookup.items():
        j=x%q
        assert j!=0 and (x-r)%primes[i]**j != 0
    counts=0
    for pattern in patterns:
        match=True
        copies=1
        for i,e,a in pattern:
            p,h=primes[i],heights[i]
            if e<=h:
                match &= x%p**e==a
                continue
            r,d0=divmod(a,p-1)
            q=lookup[i,r]
            copies*=q-h-1
            # Local k is unique if x != r, so checking all k is unnecessary.
            delta=x-r
            if not delta:
                match=False
                continue
            k=0
            while delta%p==0:
                delta//=p
                k+=1
            match &= h<=k<=q-2 and delta%p==d0+1
        assert not match
        counts+=copies
    return x,counts+sum(lookup.values())

@lru_cache(None)
def all_covered(classes):
    if not classes:
        return False
    if (1,0) in classes:
        return True
    small=min(m for m,_ in classes)
    p=next(d for d in range(2,small+1) if small%d==0)
    for b in range(p):
        reduced=set()
        for m,a in classes:
            if m%p:
                reduced.add((m,(a-b)*pow(p,-1,m)%m))
            elif a%p==b:
                reduced.add((m//p,(a-b)//p))
        if not all_covered(tuple(sorted(reduced))):
            return False
    return True

def run(module_path,path):
    spec=importlib.util.spec_from_file_location("candidate_emitter",module_path)
    emitter=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(emitter)
    ps,hs=[2,3],[1,0]
    template=[[(0,1,0)],[(1,1,1)],[(0,2,1),(1,1,0)]]
    classes=tuple(sorted(emitter.lifted_classes(ps,hs,template,odd=False)))
    assert len(classes)==len({m for m,a in classes})
    assert all_covered(classes)
    # Compare against an independently exhaustive atom test on tiny alphabets.
    for mask in range(1<<len(template)):
        pats=[pat for i,pat in enumerate(template) if mask>>i&1]
        expected=all(any(all((r[i]%(ps[i]**e)==a if e<=hs[i] else
                        r[i]*(ps[i]-1)+d[i]-1==a) for i,e,a in pat) for pat in pats)
                     for r in product(*(range(p**h) for p,h in zip(ps,hs)))
                     for d in product(*(range(1,p) for p in ps)))
        try:
            actual=tuple(sorted(emitter.lifted_classes(ps,hs,pats,odd=False)))
        except ValueError:
            assert not expected
        else:
            assert expected and all_covered(actual)
    result=concrete_hole(json.loads(Path(path).read_text()))
    print(f"Canonical mixed control: {len(classes)} classes, exact inverse-image recursion verified.")
    print("Canonical lifted hole and class count:",*result)
    return result

if __name__=="__main__":
    run(*sys.argv[1:])
