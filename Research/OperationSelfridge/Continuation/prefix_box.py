"""Search a finite box with both fixed-depth and valuation-dependent prime modes."""
from argparse import ArgumentParser
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
import json
from math import prod
from pathlib import Path
import sys

import numpy as np

parent = Path(__file__).resolve().parent.parent
checkpoint = parent if (parent / "harrington_seed.py").is_file() else parent / "selfridge3"
sys.path.insert(0, str(checkpoint))
from search_box import odd_primes, coordinates


def make_box(primes, heights):
    """An atom is (low prefix r, nonzero next digit d) for each prime."""
    alphabets=[]
    pure=[]
    for i,(p,h) in enumerate(zip(primes,heights)):
        atoms=list(product(range(p**h),range(1,p)))
        # Remove one slab at each fixed depth, and one atom at the variable depth.
        # Each addition uses a different available singleton mode.
        for e in range(1,h+1):
            phase=atoms[0][0]%(p**e)
            pure.append(((i,e,phase),))
            atoms=[s for s in atoms if s[0]%(p**e)!=phase]
        phase=atoms[0][0]*(p-1)+atoms[0][1]-1
        pure.append(((i,h+1,phase),))
        alphabets.append(atoms[1:])
    return alphabets,pure


def value(p,h,atom,mode):
    r,d=atom
    if mode==h+1:
        return r*(p-1)+d-1
    return r%(p**mode)


def exact_hole(alphabets,primes,heights,patterns):
    n=len(primes)
    active=(1<<len(patterns))-1
    transitions=[[active]*len(atoms) for atoms in alphabets]
    end=[0]*n
    for j,pat in enumerate(patterns):
        bit=1<<j
        end[max(i for i,_,_ in pat)]|=bit
        for i,e,a in pat:
            for k,atom in enumerate(alphabets[i]):
                if value(primes[i],heights[i],atom,e)!=a:
                    transitions[i][k]^=bit
    @lru_cache(maxsize=100000)
    def search(i,mask):
        if not mask:
            return (0,)*(n-i)
        possible=sorted(((mask&v,k) for k,v in enumerate(transitions[i])),key=lambda entry:entry[0].bit_count())
        for smaller,k in possible:
            if smaller&end[i]:
                continue
            suffix=search(i+1,smaller)
            if suffix is not None:
                return (k,)+suffix
        return None
    return search(0,active)


def run(a):
    primes=[p for p in odd_primes(a.rank+len(a.omit)) if p not in a.omit][:a.rank]
    heights=[0]*len(primes)
    for spec in a.depth:
        p,h=map(int,spec.split(":"))
        heights[primes.index(p)]=h
    alphabets,pure=make_box(primes,heights)
    terminal=None
    if a.leave:
        p,root,q=map(int,a.leave.split(":"))
        index=primes.index(p)
        h=heights[index]
        if q in primes or q not in odd_primes(q) or q>h+1 or not 0<=root<p**h:
            raise ValueError("The target needs a valid root and an unused odd prime no greater than the divisor count.")
        alphabets[index]=[atom for atom in alphabets[index] if atom[0]!=root]
        terminal=(index,root,q)
    sizes=[len(v) for v in alphabets]
    tables={}
    for i,(p,h) in enumerate(zip(primes,heights)):
        for e in range(1,h+2):
            phases=[value(p,h,x,e) for x in alphabets[i]]
            indices={v:j for j,v in enumerate(sorted(set(phases)))}
            inverse=sorted(indices,key=indices.get)
            table=np.array([indices[v] for v in phases],dtype=np.int32)
            stock=max(Counter(phases).values())/sizes[i]
            tables[i,e]=(table,inverse,stock)
    catalog=[tuple(zip(s,es)) for k in range(2,a.arity+1)
             for s in combinations(range(a.rank),k)
             for es in product(*(range(1,heights[i]+2) for i in s))]
    catalog.sort(key=lambda shape: -prod(tables[i,e][2] for i,e in shape))
    rng=np.random.default_rng(a.seed)
    start=coordinates(sizes,a.samples,rng)
    test=coordinates(sizes,a.holdout,rng)
    patterns=[]
    for shape in catalog:
        if not len(start):
            break
        key=np.zeros(len(start),np.int64)
        for i,e in shape:
            table,inverse,_=tables[i,e]
            key=key*len(inverse)+table[start[:,i]]
        keys,counts=np.unique(key,return_counts=True)
        winning=int(rng.choice(keys[counts==counts.max()]))
        start=start[key!=winning]
        assignments=[]
        for i,e in reversed(shape):
            table,inverse,_=tables[i,e]
            winning,d=divmod(winning,len(inverse))
            assignments.append((i,e,inverse[d]))
        patterns.append(tuple(reversed(assignments)))
    for shape in patterns:
        if not len(test):break
        keep=np.ones(len(test),dtype=bool)
        for i,e,p in shape:
            table,inverse,_=tables[i,e]
            keep &= table[test[:,i]]==inverse.index(p)
        test=test[~keep]
    hole=exact_hole(alphabets,primes,heights,patterns)
    witness=None if hole is None else [alphabets[i][x] for i,x in enumerate(hole)]
    if witness is not None:
        assert all(any(value(primes[i],heights[i],witness[i],e)!=p for i,e,p in pat)
                   for pat in pure+patterns)
    result={"primes":primes,"heights":heights,"samples":a.samples,"holdout_samples":a.holdout,
            "training_misses":len(start),"holdout_misses":len(test),"patterns_after_unary":len(patterns),
            "uncovered_atom_word":witness,"terminal":terminal,"seed":a.seed}
    print(json.dumps(result),flush=True)
    Path(a.output).write_text(json.dumps(result|{"pure":pure,"patterns":patterns},separators=(",",":"))+"\n")


if __name__=="__main__":
    p=ArgumentParser()
    p.add_argument("--rank",type=int,default=20)
    p.add_argument("--depth",action="append",default=[])
    p.add_argument("--omit",type=int,action="append",default=[])
    p.add_argument("--leave",help="primary prime:root:unused terminal prime")
    p.add_argument("--arity",type=int,default=5)
    p.add_argument("--samples",type=int,default=250000)
    p.add_argument("--holdout",type=int,default=200000)
    p.add_argument("--seed",type=int,default=2707)
    p.add_argument("--output",default="selfridge4/prefix_candidate.json")
    run(p.parse_args())
