"""Counterexample-guided SAT refits for existing valuation-box patterns."""
import argparse
from collections import defaultdict
from itertools import combinations
import json
from math import prod
from pathlib import Path
import sys
import time

import numpy as np
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver

parent = Path(__file__).resolve().parent.parent
checkpoint = parent if (parent / "harrington_seed.py").is_file() else parent / "selfridge3"
sys.path.insert(0, str(checkpoint))
from search_box import coordinates, first_hole, point_misses


def full_pattern(rank, support, digits):
    values = [-1] * rank
    for i, v in zip(support, digits):
        values[i] = v
    return values


def find_holes(points, sizes, model):
    alive = np.ones(len(points),dtype=bool)
    for support, digits in model.items():
        selected = np.flatnonzero(alive)
        if len(selected) == 0:
            break
        match = np.ones(len(selected),dtype=bool)
        for i,v in zip(support,digits):
            match &= points[selected,i] == v
        alive[selected[match]] = False
    return points[alive]


def phase_ids(support, points, sizes):
    labels = np.zeros(len(points), dtype=np.int64)
    for i in support:
        labels = labels*sizes[i] + points[:,i]
    return labels


def unpack_phase(support, label, sizes):
    digits=[]
    for i in reversed(support):
        label, digit=divmod(label,sizes[i])
        digits.append(digit)
    return tuple(reversed(digits))


def menus_for_holes(holes, sizes, reserve, menus, points):
    if not len(holes):
        return
    for support in reserve:
        values, counts=np.unique(phase_ids(support,holes,sizes),return_counts=True)
        best=np.argsort(counts,kind="stable")[-4:]
        for j in best:
            if counts[j] >= 2:
                menus[support].add(unpack_phase(support,int(values[j]),sizes))
    # Give every observed hole multiple escape options, even when its projection is unique.
    for idx, row in enumerate(holes):
        choices = reserve[(idx*97)%len(reserve):]+reserve[:(idx*97)%len(reserve)]
        for support in choices[:5]:
            menus[support].add(tuple(int(row[i]) for i in support))


def solve(points, sizes, menus, current, millis, changes):
    ids=IDPool()
    requirements=[[] for _ in range(len(points))]
    ph={}
    start=time.monotonic()
    with Solver(name="cadical195") as solver:
        for support, options in menus.items():
            indices=phase_ids(support,points,sizes)
            order=np.argsort(indices)
            sorted_labels=indices[order]
            group=[]
            for digits in sorted(options):
                target=0
                for i,v in zip(support,digits):target=target*sizes[i]+v
                low,high=np.searchsorted(sorted_labels,[target,target+1])
                if low==high and current.get(support)!=digits:
                    continue
                ident=ids.id((support,digits))
                ph[ident]=(support,digits)
                group.append(ident)
                for j in order[low:high]:
                    requirements[int(j)].append(ident)
            if len(group)>1:
                solver.append_formula(CardEnc.atmost(group,1,vpool=ids,encoding=EncType.seqcounter).clauses)
        solver.append_formula(requirements)
        incumbents=[i for i,(s,d) in ph.items() if current.get(s)==d]
        if 0<=changes<len(incumbents):
            solver.append_formula(CardEnc.atmost([-i for i in incumbents],changes,vpool=ids,encoding=EncType.seqcounter).clauses)
        hints=[i if current.get(s)==d else -i for i,(s,d) in ph.items()]
        solver.set_phases(hints)
        from threading import Timer
        timer=Timer(millis/1000,solver.interrupt)
        timer.start()
        try:
            sat=solver.solve_limited(expect_interrupt=True)
            model=solver.get_model() if sat else None
        finally:
            timer.cancel()
        data={ph[i][0]:ph[i][1] for i in model if i in ph} if model else None
        return sat,data,len(ph),time.monotonic()-start


def run(args):
    src=json.loads(Path(args.input).read_text())
    sizes=src["sizes"]
    r=len(sizes)
    current={}
    menu=defaultdict(set)
    for pat in src["patterns"]:
        s=tuple(i for i,v in enumerate(pat) if v>=0)
        d=tuple(pat[i] for i in s)
        current[s]=d
        menu[s].add(d)
    reserve=sorted(set(current)|set(combinations(range(r),2))|
                   set(combinations(range(r),3)),key=lambda s: (prod(sizes[i] for i in s),s))
    rng=np.random.default_rng(args.seed)
    tracked=coordinates(sizes,args.training,rng)
    test=coordinates(sizes,args.holdout,rng)
    tracked=np.vstack([tracked,np.array([src["uncovered_point"]],dtype=np.int32)])
    baseline=find_holes(test,sizes,current)
    print(json.dumps({"initial_test_holes":len(baseline),"seed":args.seed}),flush=True)
    best=len(baseline)
    for it in range(args.rounds):
        batch=coordinates(sizes,args.adversary,rng)
        holes=find_holes(batch,sizes,current)
        prefix=holes[:args.keep]
        if len(prefix):
            tracked=np.unique(np.vstack([tracked,prefix]),axis=0)
        holes=find_holes(tracked,sizes,current)
        menus_for_holes(holes,sizes,reserve,menu,tracked)
        sat,proposed,variables,elapsed=solve(tracked,sizes,menu,current,args.millis,args.changes)
        if sat:
            current=proposed
            assert not len(find_holes(tracked,sizes,current))
            miss=len(find_holes(test,sizes,current))
            patterns=[full_pattern(r,s,d) for s,d in sorted(current.items())]
            hole=first_hole(sizes,patterns)
            assert hole is None or point_misses(hole,patterns)
            print(json.dumps({"iteration":it,"sat":True,"tracked":len(tracked),"variables":variables,
                              "active_patterns":len(patterns),"holdout_misses":miss,
                              "hole":hole,"elapsed":round(elapsed,2)}),flush=True)
            if miss<best or it==0:
                best=min(best,miss)
                Path(args.output).write_text(json.dumps(src|{"seed":args.seed,"patterns":patterns,
                    "training_samples":len(tracked),"training_misses":0,"holdout_samples":len(test),
                    "holdout_misses":miss,"uncovered_point":hole,"iteration":it},separators=(",",":"))+"\n")
            if hole is None:
                return
            tracked=np.unique(np.vstack([tracked,np.array([hole],dtype=np.int32)]),axis=0)
        else:
            print(json.dumps({"iteration":it,"status":sat,"tracked":len(tracked),"variables":variables,
                              "elapsed":round(elapsed,2)}),flush=True)
            if sat is False:
                return

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--input",default="selfridge3/rank20_candidate.json")
    p.add_argument("--output",default="selfridge4/refit_rank20.json")
    p.add_argument("--training",type=int,default=12000)
    p.add_argument("--holdout",type=int,default=200000)
    p.add_argument("--adversary",type=int,default=30000)
    p.add_argument("--keep",type=int,default=220)
    p.add_argument("--rounds",type=int,default=12)
    p.add_argument("--seed",type=int,default=2707)
    p.add_argument("--millis",type=int,default=20000)
    p.add_argument("--changes",type=int,default=-1)
    run(p.parse_args())
