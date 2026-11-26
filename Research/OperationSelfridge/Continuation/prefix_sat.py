"""Counterexample-guided exact finite prefix-box model with arbitrary phase changes."""
from argparse import ArgumentParser
from itertools import combinations, product
import json
from pathlib import Path
from threading import Timer
from time import monotonic

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver

from prefix_box import exact_hole, make_box, odd_primes, value


def solve(primes,heights,arity,initial_hole,max_rounds,seconds,directory,free_unaries):
    if free_unaries:
        alphabets=[list(product(range(p**h),range(1,p))) for p,h in zip(primes,heights)]
        pure=[]
    else:
        alphabets,pure=make_box(primes,heights)
    sizes=[len(atoms) for atoms in alphabets]
    slots=[tuple(zip(subset,modes))
           for k in range(1 if free_unaries else 2,arity+1) for subset in combinations(range(len(primes)),k)
           for modes in product(*(range(1,heights[i]+2) for i in subset))]
    phases={(i,e):sorted({value(p,h,atom,e) for atom in alphabets[i]})
            for i,(p,h) in enumerate(zip(primes,heights)) for e in range(1,h+2)}
    column={(i,e):[value(p,h,atom,e) for atom in alphabets[i]]
            for i,(p,h) in enumerate(zip(primes,heights)) for e in range(1,h+2)}
    variables=IDPool()
    known={}
    nclauses=0
    with Solver(name="cadical195") as solver:
        for shape_index,slot in enumerate(slots):
            for i,e in slot:
                opts=[variables.id((shape_index,i,phase)) for phase in phases[i,e]]
                solver.append_formula(CardEnc.equals(opts,bound=1,vpool=variables,encoding=EncType.seqcounter).clauses)
        observations=set()

        def add(word):
            nonlocal nclauses
            if word in observations:
                return
            observations.add(word)
            choices=[]
            for s,slot in enumerate(slots):
                projection=tuple(column[i,e][word[i]] for i,e in slot)
                key=(s,projection)
                hit=known.get(key)
                if hit is None:
                    hit=variables.id(("matches",key))
                    known[key]=hit
                    for (i,_),phase in zip(slot,projection):
                        solver.add_clause([-hit,variables.id((s,i,phase))])
                    nclauses+=len(slot)
                choices.append(hit)
            solver.add_clause(choices)
            nclauses+=1

        add(tuple(initial_hole if initial_hole is not None else (0,)*len(primes)))
        deadline=monotonic()+seconds
        result=None
        for turn in range(max_rounds):
            left=deadline-monotonic()
            if left<=0:
                break
            timer=Timer(left,solver.interrupt)
            timer.start()
            try:
                result=solver.solve_limited(expect_interrupt=True)
                assignment=solver.get_model() if result else None
            finally:
                timer.cancel()
            if result is False:
                report={"status":"unsat_finite_constraints","slots":len(slots),
                        "witness_constraints":len(observations),"primes":primes,"heights":heights,
                        "maximum_arity":arity,"free_unaries":free_unaries}
                Path(directory).write_text(json.dumps(report|{"observation_words":sorted(observations)})+"\n")
                print(json.dumps(report),flush=True)
                return
            if result is None:
                break
            yes={x for x in assignment if x>0}
            patterns=[tuple((i,e,next(v for v in phases[i,e] if variables.id((s,i,v)) in yes))
                            for i,e in slot) for s,slot in enumerate(slots)]
            hole=exact_hole(alphabets,primes,heights,patterns)
            if hole is None:
                print(json.dumps({"status":"box_cover","slots":len(slots),"witness_constraints":len(observations)}),flush=True)
                Path(directory).write_text(json.dumps({"status":"box_cover","primes":primes,"heights":heights,
                                                       "pure":pure,"patterns":patterns})+"\n")
                return
            if turn%25==0:
                print(json.dumps({"round":turn,"constraints":len(observations),"slots":len(slots),
                                  "matching_clauses":nclauses,"new_hole":hole}),flush=True)
            # Force a cross-section through a certified hole by varying one coordinate.
            assert hole not in observations
            pos=turn%len(primes)
            for v in range(sizes[pos]):
                add(hole[:pos]+(v,)+hole[pos+1:])
        print(json.dumps({"status":"bounded_incomplete","witness_constraints":len(observations),
                          "slots":len(slots),"last_solver_result":result}),flush=True)


if __name__=="__main__":
    parser=ArgumentParser()
    parser.add_argument("--rank",type=int,default=8)
    parser.add_argument("--depth",action="append",default=[])
    parser.add_argument("--arity",type=int,default=3)
    parser.add_argument("--rounds",type=int,default=100)
    parser.add_argument("--seconds",type=float,default=40)
    parser.add_argument("--input")
    parser.add_argument("--free-unaries",action="store_true")
    parser.add_argument("--output",default="selfridge4/prefix_sat_result.json")
    a=parser.parse_args()
    if a.input:
        data=json.loads(Path(a.input).read_text())
        ps,hs=data["primes"],data["heights"]
        if a.free_unaries:
            initial=[root*(p-1)+digit-1 for p,(root,digit) in zip(ps,data["uncovered_atom_word"])]
        else:
            A,_=make_box(ps,hs)
            initial=[alph.index(tuple(atom)) for alph,atom in zip(A,data["uncovered_atom_word"])]
    else:
        ps=odd_primes(a.rank)
        hs=[0]*len(ps)
        for token in a.depth:
            p,h=map(int,token.split(":"))
            hs[ps.index(p)]=h
        initial=None
    solve(ps,hs,a.arity,initial,a.rounds,a.seconds,a.output,a.free_unaries)
