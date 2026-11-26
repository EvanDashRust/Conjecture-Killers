"""Repair actual congruences with permanent integer counterexamples."""
import argparse
import numpy as np
from fractions import Fraction
from math import prod
from pathlib import Path
import random
from time import monotonic

from pysat.card import CardEnc
from pysat.examples.rc2 import RC2
from pysat.formula import IDPool, WCNF

from prefix_sat import read, write
from catalogue_obstruction import local_cap
from refine_harrington import sample, without
from search_harrington import decompose, local_witness, seed


def weighted_core(moduli, primes):
    # Positive certificate for failing the two-low-vertices condition:
    # find U for which all but one prime have high load, or peel for every exception.
    edges = []
    for m in moduli:
        powers = {primes[i]:q for i,q in decompose(m,primes) if primes[i]>17}
        if len(powers)>=2:
            edges.append(powers)
    vertices=set(q for edge in edges for q in edge)
    for exceptional in sorted(vertices):
        remain = set(vertices)
        while len(remain)>1:
            loads = {q:sum((Fraction(1,e[q]) for e in edges if q in e and e.keys()<=remain),
                           Fraction(0)) for q in remain}
            eligible = sorted(q for q in remain if q!=exceptional and
                              loads[q]<=max(Fraction(1,6),Fraction(5,q)))
            if not eligible:
                return {"passes_necessary_test":True,"subset":sorted(remain),"exception":exceptional,
                        "loads":{str(q):str(loads[q]) for q in sorted(remain)}}
            remain.remove(eligible[0])
    return {"passes_necessary_test":False}


def repair(current, required, movable):
    pool, formula = IDPool(), WCNF()
    fixed = [(m,a) for m,a in current.items() if m not in movable]
    active = [x for x in required if all(x%m!=a for m,a in fixed)]
    opts = {}
    for m in movable:
        residues = {x%m for x in active}
        residues.add(current[m])
        lut = {r:pool.id((m,r)) for r in sorted(residues)}
        formula.extend(CardEnc.equals(list(lut.values()),1,vpool=pool).clauses)
        formula.append([lut[current[m]]],weight=1)
        opts[m]=lut
    for x in active:
        formula.append([opts[m][x%m] for m in movable])
    with RC2(formula) as solver:
        assignment = solver.compute()
    if assignment is None:
        return None
    yes = set(assignment)
    new = dict(current)
    for m,lut in opts.items():
        new[m]=next(r for r,lit in lut.items() if lit in yes)
    assert all(any(x%m==a for m,a in new.items()) for x in required)
    return new


def enlarge(initial, primes, count, minimum):
    """Greedy phases for unused labels ranked by their capacity on the seed-free product."""
    eligible=[]
    for m in range(minimum | 1,max(50_001,minimum+65_000),2):
        if m in initial:
            continue
        factors=decompose(m,primes)
        if factors is not None:
            capacity=prod(local_cap(primes[i],power) for i,power in factors)
            eligible.append((capacity,m,factors))
    selected=sorted(eligible,reverse=True)[:count]
    old=[(m,a,decompose(m,primes)) for m,a in initial.items()]
    caps=[max([1]+[v for _,_,f in old+selected for k,v in f if k==i])
          for i in range(len(primes))]
    rng=np.random.default_rng(23423)
    residual=without(sample(rng,caps,100000),old)
    from refine_harrington import assemble,labels
    for _,m,factors in selected:
        if len(residual):
            values=labels(residual,factors)
            best=int(np.bincount(values).argmax())
            _,a=assemble(best,factors)
            residual=residual[values!=best]
        else:
            a=int(rng.integers(m))
        initial[m]=a


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--output",required=True)
    ap.add_argument("--move-seed",action="store_true")
    ap.add_argument("--rounds",type=int,default=50)
    ap.add_argument("--seconds",type=float,default=60)
    ap.add_argument("--integer", action="append",default=[])
    ap.add_argument("--extend",type=int,default=0)
    ap.add_argument("--extension-min",type=int,default=3797)
    a=ap.parse_args()
    folder=Path(__file__).resolve().parent
    out=Path(a.output)
    base=read(folder/"harrington_reoptimized.json")
    original=dict(seed())
    initial=dict(original)
    initial.update(base["additions"])
    primes=base["primes"]
    if a.extend:
        if out.exists():
            initial.update(read(out)["classes"])
        else:
            enlarge(initial,primes,a.extend,a.extension_min)
    factors={m:decompose(m,primes) for m in initial}
    caps=[max([1]+[power for ff in factors.values() for j,power in ff if j==i])
          for i in range(len(primes))]
    extra=[m for m in initial if m not in original]
    if out.exists():
        state=read(out)
        if state["move_seed"]!=a.move_seed or state.get("extend",0)!=a.extend or state.get("extension_min",3797)!=a.extension_min:
            raise ValueError("Seed policy differs from saved run.")
        current=dict(state["classes"])
    else:
        requirements=[read(folder/f)["uncovered_integer"] for f in
                      ("harrington_mixed.json","harrington_reoptimized.json")]
        current=dict(initial)
        if a.move_seed:
            current[9]=int(requirements[-1])%9
            assert current[9]!=original[9]
        state=dict(version=1,extend=a.extend,extension_min=a.extension_min,move_seed=a.move_seed,primes=primes,integers=requirements,
                   classes=list(current.items()),holes=[],runs=0,
                   weighted_test=weighted_core(extra,primes),phase_changes=[])
    state["integers"]=list(dict.fromkeys(state["integers"]+list(map(str,map(int,a.integer)))))
    start=monotonic()
    for _ in range(a.rounds):
        if monotonic()-start>a.seconds: break
        xset=list(map(int,state["integers"]))
        rng=random.Random(23423+state["runs"])
        movable=rng.sample(extra, min(56,len(extra)))
        if a.move_seed:
            movable += [m for m in [15,21,25,35] if m in original]
        new=repair(current,xset,movable)
        state["runs"]+=1
        if new is None:
            state["status"]="window_unsat"
            write(out,state)
            continue
        changed=[m for m in new if new[m]!=current[m]]
        current=new
        state.update(classes=list(current.items()),status="model_pending_check")
        state["phase_changes"].append(changed)
        write(out,state)
        hole=local_witness(primes,caps,[(m,r,factors[m]) for m,r in current.items()])
        if hole is None:
            state["status"]="exact_cover_candidate"
            write(out,state)
            break
        assert hole not in xset and all(hole%m!=r for m,r in current.items())
        state["holes"].append(str(hole))
        state["integers"].append(str(hole))
        state["status"]="exact_hole"
        write(out,state)
    print(out.name,state["status"],state["runs"],len(state["integers"]),
          "required ints; weighted condition",state["weighted_test"])
if __name__=="__main__":
    main()
