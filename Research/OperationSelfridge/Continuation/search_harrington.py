"""Search actual odd congruences while preserving Harrington's near-cover."""
import argparse
from itertools import combinations
import json
from math import isqrt
from pathlib import Path
import sys

import numpy as np

parent = Path(__file__).resolve().parent.parent
checkpoint = parent if (parent / "harrington_seed.py").is_file() else parent / "selfridge3"
sys.path.insert(0, str(checkpoint))
from harrington_seed import crt, seed
from search_box import first_hole


def primes_through(bound):
    return [p for p in range(3,bound+1,2)
            if all(p%d for d in range(3,isqrt(p)+1,2))]


def decompose(modulus, primes):
    constraints=[]
    for i,p in enumerate(primes):
        power=1
        while modulus%p==0:
            modulus//=p
            power*=p
        if power>1:
            constraints.append((i,power))
    if modulus!=1:
        return None
    return constraints


def labels(points, factors):
    output=np.zeros(len(points),dtype=np.int64)
    for i,power in factors:
        output=output*power+points[:,i]%power
    return output


def local_witness(primes, maximum_powers, family):
    # Expand each prime coordinate in low-to-high digits. Every congruence
    # fixes a prefix in each participating coordinate.
    digit_sizes=[]
    offsets=[]
    for p, power in zip(primes,maximum_powers):
        offsets.append(len(digit_sizes))
        while power>1:
            digit_sizes.append(p)
            power//=p
    shapes=[]
    for _, residue, factors in family:
        pattern=[-1]*len(digit_sizes)
        for i,power in factors:
            k=offsets[i]
            p=primes[i]
            a=residue%power
            while power>1:
                a,pattern[k]=divmod(a,p)
                k+=1
                power//=p
        shapes.append(pattern)
    found=first_hole(digit_sizes,shapes)
    if found is None:
        return None
    parts=[]
    for i,(p,power) in enumerate(zip(primes,maximum_powers)):
        k=offsets[i]
        residue, weight=0,1
        while weight<power:
            residue+=weight*found[k]
            weight*=p
            k+=1
        if power>1:
            parts.append((power,residue))
    _,x=crt(*parts)
    assert all(x%m!=a for m,a,_ in family)
    return x


def run(args):
    primes=primes_through(args.prime_max)
    old=[(m,a,decompose(m,primes)) for m,a in seed()]
    old_keys={m for m,_,_ in old}
    possible=[]
    for m in range(3,args.mod_max+1,2):
        if m not in old_keys:
            factors=decompose(m,primes)
            if factors is not None:
                possible.append((m,factors))
    caps=[1]*len(primes)
    for factors in (f for _,_,f in old):
        for i,power in factors:
            caps[i]=max(caps[i],power)
    for _,factors in possible:
        for i,power in factors:
            caps[i]=max(caps[i],power)
    rng=np.random.default_rng(args.seed)
    def points(count):
        return np.column_stack([rng.integers(0,power,count,dtype=np.int64) for power in caps])
    def residual(data,family):
        for m,a,factors in family:
            if not len(data):
                break
            match=np.ones(len(data),dtype=bool)
            for i,power in factors:
                match &= data[:,i]%power==a%power
            data=data[~match]
        return data
    train=points(args.samples)
    test=points(args.holdout)
    train=residual(train,old)
    test=residual(test,old)
    print(json.dumps({"seed_training_holes":len(train),"seed_holdout_holes":len(test),
                      "allowed_additions":len(possible)}),flush=True)
    extra=[]
    for m,factors in possible:
        if not len(train):
            break
        group=labels(train,factors)
        values,counts=np.unique(group,return_counts=True)
        target=int(rng.choice(values[counts==counts.max()]))
        train=train[group!=target]
        pairs=[]
        for i,power in reversed(factors):
            target,remainder=divmod(target,power)
            pairs.append((power,remainder))
        modulus,residue=crt(*pairs)
        assert modulus==m
        extra.append((m,residue,factors))
    x=local_witness(primes,caps,old+extra)
    result={"primes":primes,"modulus_cap":args.mod_max,"seed":args.seed,
            "samples":args.samples,"training_misses":len(train),
            "holdout_samples":args.holdout,"holdout_misses":len(residual(test,extra)),
            "seed_classes":len(old),"added_classes":len(extra),
            "mixed_additions":sum(sum(primes[i]>17 for i,_ in f)>=2 for _,_,f in extra),
            "uncovered_integer":None if x is None else str(x)}
    Path(args.output).write_text(json.dumps(result|{"additions":[[m,a] for m,a,_ in extra]},
                                            separators=(",",":"))+"\n")
    print(json.dumps(result),flush=True)


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--prime-max",type=int,default=73)
    p.add_argument("--mod-max",type=int,default=800000)
    p.add_argument("--samples",type=int,default=200000)
    p.add_argument("--holdout",type=int,default=200000)
    p.add_argument("--seed",type=int,default=4266)
    p.add_argument("--output",default="selfridge4/harrington_mixed.json")
    run(p.parse_args())
