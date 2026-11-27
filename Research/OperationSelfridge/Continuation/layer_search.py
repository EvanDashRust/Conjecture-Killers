"""Counterexample feedback for a common auxiliary modulus with many patterns per row."""
import argparse
from collections import Counter
from itertools import combinations, product
from math import prod
from pathlib import Path
import random

from prefix_box import exact_hole, make_box, value
from prefix_lift import matches, crt
from prefix_sat import atoms_of,read,write


def run(a):
    data=read(a.base)
    ps,hs=data["primes"],data["heights"]
    alph,pure=make_box(ps,hs)
    base=data["patterns"]
    q=a.q
    from math import gcd
    assert q>1 and q%2 and gcd(q,prod(ps))==1 and not data.get("terminal")
    # Use a common exit auxiliary Q distinct from q. Q may be fixed throughout.
    from prefix_lift import is_prime
    Q=max([q,*ps,*hs])+1
    while not is_prime(Q):Q+=1
    out=Path(a.output)
    if out.exists():
        state=read(out)
        assert (ps,hs,q,a.arity)==(state["primes"],state["heights"],state["q"],state["arity"])
    else:
        state=dict(schema="multi-pattern-rough-row-1",primes=ps,heights=hs,q=q,exit_prime=Q,
                   arity=a.arity,base_patterns=base,pure=pure,rows=[[] for _ in range(q-1)],
                   exact_holes=[],integers=[],round=0,status="initialized")
    dims={(i,e):Counter(value(p,h,x,e) for x in alph[i]) for i,(p,h) in enumerate(zip(ps,hs))
          for e in range(1,h+2)}
    shapes=[tuple(zip(S,es)) for k in range(1,a.arity+1) for S in combinations(range(len(ps)),k)
            for es in product(*(range(1,hs[i]+2) for i in S))]
    used={tuple((i,e) for i,e,v in pat) for row in state["rows"] for pat in row}
    def choose(w):
        best=None
        for s in shapes:
            if s in used:continue
            phase=[(i,e,value(ps[i],hs[i],w[i],e)) for i,e in s]
            # Conditional digit-domain mass within the current fixed-unary complement.
            score=prod(dims[i,e][v]/len(alph[i]) for i,e,v in phase)
            if best is None or score>best[0]:best=(score,s,phase)
        return best
    def require(j,w):
        if any(matches(ps,hs,w,p) for p in state["rows"][j-1]):return True
        proposal=choose(w)
        if proposal is None:return False
        _,s,pat=proposal
        state["rows"][j-1].append(pat)
        used.add(s)
        return True
    pending=state.pop("pending_obligation",None)
    if pending:
        if not require(pending["row"],pending["atoms"]):
            state.update(status="greedy_catalogue_spent",pending_obligation=pending)
            write(out,state)
            return
        state["integers"].append(pending["integer"])
        state["exact_holes"].append(pending)
        write(out,state)
    for file in a.integers:
        integers=read(file)
        for x in map(int,integers["integers"]):
            sx=str(x)
            if sx in state["integers"]:continue
            w=atoms_of(x,ps,hs)
            if x%q and not any(matches(ps,hs,w,p) for p in base+list(pure)):
                if not require(x%q,w):
                    state["status"]="greedy_catalogue_spent";write(out,state);return
            state["integers"].append(sx)
    for _ in range(a.rounds):
        j=1+state["round"]%(q-1)
        state["round"]+=1
        pats=base+state["rows"][j-1]
        hole=exact_hole(alph,ps,hs,pats)
        if hole is None:
            state.setdefault("complete_rows",[])
            if j not in state["complete_rows"]:state["complete_rows"].append(j)
            if len(state["complete_rows"])==q-1:
                state["status"]="box_cover";write(out,state);return
            continue
        w=[A[k] for A,k in zip(alph,hole)]
        assert not any(matches(ps,hs,w,p) for p in list(pure)+pats)
        _,x=crt([(Q,1),(q,j)]+[(p**(h+1),r+d*p**h) for p,h,(r,d) in zip(ps,hs,w)])
        state["exact_holes"].append({"row":j,"atoms":w,"integer":str(x),
                                     "prior_row_size":len(state["rows"][j-1])})
        assert str(x) not in state["integers"]
        state["integers"].append(str(x))
        if not require(j,w):
            state["status"]="greedy_catalogue_spent";write(out,state);return
        state["status"]="added_pattern"
        write(out,state)
    print("repairs",len(state["exact_holes"]),"assigned shapes",len(used),"rows",q-1,flush=True)

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--base",default=str(Path(__file__).with_name("prefix_candidate.json")))
    p.add_argument("--output",required=True)
    p.add_argument("--integers",action="append",default=[])
    p.add_argument("--q",type=int,default=79)
    p.add_argument("--arity",type=int,default=3)
    p.add_argument("--rounds",type=int,default=300)
    run(p.parse_args())
