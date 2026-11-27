"""Coordinate descent on actual congruence residues, with the seed fixed."""
import argparse
import json
from math import prod
from pathlib import Path
from collections import Counter

import numpy as np

from search_harrington import crt, decompose, labels, local_witness, seed


def sample(rng, caps, size):
    return np.column_stack([rng.integers(0,power,size,dtype=np.int64) for power in caps])


def without(points, family):
    for _, a, factors in family:
        if not len(points):
            break
        agree=np.ones(len(points),dtype=bool)
        for i,d in factors:
            agree &= points[:,i]%d==a%d
        points=points[~agree]
    return points


def assemble(label, factors):
    data=[]
    for _,power in reversed(factors):
        label,residue=divmod(label,power)
        data.append((power,residue))
    return crt(*data)


def encoded(residue, factors):
    label=0
    for _,p in factors: label=label*p+residue%p
    return label


def optimize(training, holdout, current, rounds, rng, save):
    tables=[labels(training,f).astype(np.int32) for _,_,f in current]
    phases=[encoded(a,f) for _,a,f in current]
    covered=np.zeros(len(training),dtype=np.int16)
    for table,old in zip(tables,phases):
        covered += table==old
    baseline=len(without(holdout,current))
    print(json.dumps({"stage":"start","training":len(training),"holdout":len(holdout),
                      "baseline_misses":baseline}),flush=True)
    best=baseline+1
    for iteration in range(rounds):
        changed=0
        for index in rng.permutation(len(tables)):
            table=tables[index]
            old=phases[index]
            covered-=table==old
            open_labels=table[covered==0]
            if len(open_labels):
                counts=np.bincount(open_labels)
                optimum=int(counts.argmax())
                existing=0 if old>=len(counts) else int(counts[old])
                if counts[optimum]>existing:
                    phases[index]=optimum
                    changed+=1
            covered+=table==phases[index]
        updated=[(*assemble(value,factors),factors) for (_,_,factors),value in zip(current,phases)]
        miss=len(without(holdout,updated))
        print(json.dumps({"round":iteration,"changed":changed,"training_misses":int((covered==0).sum()),
                          "holdout_misses":miss}),flush=True)
        if miss<best:
            best=miss
            save(updated,miss,iteration,baseline)
        if not changed:
            break


def main():
    p=argparse.ArgumentParser()
    p.add_argument("--input",default="selfridge4/harrington_mixed.json")
    p.add_argument("--output",default="selfridge4/harrington_reoptimized.json")
    p.add_argument("--train",type=int,default=500_000)
    p.add_argument("--holdout",type=int,default=350_000)
    p.add_argument("--rounds",type=int,default=9)
    p.add_argument("--seed",type=int,default=17026)
    args=p.parse_args()
    data=json.loads(Path(args.input).read_text())
    primes=data["primes"]
    old=[(m,r,decompose(m,primes)) for m,r in seed()]
    extra=[(m,r,decompose(m,primes)) for m,r in data["additions"]]
    caps=[1]*len(primes)
    for _,_,f in old+extra:
        for i,power in f:
            caps[i]=max(caps[i],power)
    rng=np.random.default_rng(args.seed)
    training=without(sample(rng,caps,args.train),old)
    holdout=without(sample(rng,caps,args.holdout),old)
    def save(updated,miss,iteration,baseline):
        x=local_witness(primes,caps,old+updated)
        result={**data,"seed":args.seed,"samples":args.train,"holdout_samples":args.holdout,
                "holdout_misses":miss,"initial_holdout_misses":baseline,"iteration":iteration,
                "uncovered_integer":None if x is None else str(x),
                "additions":[[m,r] for m,r,_ in updated]}
        result.pop("training_misses",None)
        Path(args.output).write_text(json.dumps(result,separators=(",",":"))+"\n")
    optimize(training,holdout,extra,args.rounds,rng,save)


if __name__=="__main__":
    main()
