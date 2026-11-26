"""Find and independently verify product subsets of exact holes in a prefix catalogue."""
import argparse
from collections import Counter
from fractions import Fraction
from math import prod
from pathlib import Path
import json

from prefix_box import make_box,value
from prefix_sat import write,read
from pysat.card import CardEnc
from pysat.formula import IDPool
from pysat.solvers import Solver


def data_for(data):
    ps,hs=data["primes"],data["heights"]
    alph,pure=make_box(ps,hs)
    assert not data.get("terminal") and json.loads(json.dumps(pure))==data["pure"]
    groups={}
    for i,(p,h) in enumerate(zip(ps,hs)):
        for e in range(1,h+2):
            for k,a in enumerate(alph[i]):
                groups.setdefault((i,e,value(p,h,a,e)),[]).append(k)
    return alph,groups


def analyse(box,hs,groups):
    sizes=[m.bit_count() for m in box]
    caps=[[0]*h for h in hs]
    for (i,e,v),indices in groups.items():
        if e<=hs[i]:
            caps[i][e-1]=max(caps[i][e-1],sum((box[i]>>a)&1 for a in indices))
    return sizes,caps


def cost(sizes,caps):
    return prod(1+Fraction(sum(c)+1,s) for s,c in zip(sizes,caps))


def verify(data,box):
    alph,groups=data_for(data)
    hs=data["heights"]
    assert len(box)==len(alph)
    assert all(0<m<1<<len(a) for m,a in zip(box,alph))
    for pat in data["patterns"]:
        assert any(all(not (box[i]>>k&1) for k in groups[i,e,v]) for i,e,v in pat)
    return cost(*analyse(box,hs,groups))


def find(pats,alph,groups,sizes,caps,conflicts):
    pool=IDPool()
    atom=[[pool.id(("atom",i,k)) for k in range(len(a))] for i,a in enumerate(alph)]
    with Solver(name="cadical195") as sat:
        for i,(vs,n) in enumerate(zip(atom,sizes)):
            sat.append_formula(CardEnc.atleast(vs,n,vpool=pool).clauses)
        for t,indices in groups.items():
            i,e,v=t
            blocked=pool.id(t)
            for k in indices:
                sat.add_clause([-blocked,-atom[i][k]])
            if e<=len(caps[i]) and caps[i][e-1]<len(indices):
                sat.append_formula(CardEnc.atmost([atom[i][k] for k in indices],
                                   caps[i][e-1],vpool=pool).clauses)
        for pat in pats:
            sat.add_clause([pool.id(tuple(t)) for t in pat])
        sat.conf_budget(conflicts)
        if sat.solve_limited() is not True:return None
        yes=set(sat.get_model())
        return [sum(1<<k for k,v in enumerate(vs) if v in yes) for vs in atom]


def main():
    p=argparse.ArgumentParser()
    p.add_argument("--candidate",default=str(Path(__file__).with_name("prefix_candidate.json")))
    p.add_argument("--box",required=True)
    p.add_argument("--steps",type=int,default=0)
    p.add_argument("--conflicts",type=int,default=600)
    args=p.parse_args()
    data=read(args.candidate); original=read(args.box)
    box=[int(x,16) for x in original["masks"]]
    best=verify(data,box)
    alph,g=data_for(data)
    for step in range(args.steps):
        sizes,caps=analyse(box,data["heights"],g)
        trials=[]
        for i,a in enumerate(alph):
            if sizes[i]<len(a):
                ns=sizes[:];ns[i]+=1
                trials.append((cost(ns,caps),ns,caps))
            for e,n in enumerate(caps[i]):
                if n>1:
                    nc=[c[:] for c in caps];nc[i][e]-=1
                    trials.append((cost(sizes,nc),sizes,nc))
        for target,ns,nc in sorted(trials):
            proposal=find(data["patterns"],alph,g,ns,nc,args.conflicts)
            if proposal is None:continue
            price=verify(data,proposal)
            if price<best:
                box,best=proposal,price
                original["masks"]=[hex(x) for x in box]
                write(args.box,original)
                print(step,float(best),flush=True)
                break
        else:
            break
    print("Uncovered product verified; exact old-mode sum",best,float(best))
if __name__=="__main__":
    main()
