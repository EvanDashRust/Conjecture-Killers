"""Release every unary phase in a high-rank incumbent; force one old unary to change."""
from argparse import ArgumentParser
from itertools import product
from pathlib import Path
from random import Random
from time import monotonic

from pysat.card import CardEnc
from pysat.formula import IDPool
from pysat.solvers import Solver
from prefix_box import exact_hole
from prefix_incumbent import pack,projection,shape
from prefix_lift import matches,validate
from prefix_sat import actual_witness,atoms_of,key,read,write


def initial(base,bank):
    ps,hs=base["primes"],base["heights"]
    slots=[shape(p) for p in base["pure"]]+base["slots"]
    phases=[[v for _,_,v in p] for p in base["pure"]]+base["latest_phases"]
    integers=sorted(set(map(int,bank["integers"]))|set(map(int,base["integers"])))
    words=list(dict.fromkeys([key(w) for w in base["observations"]]+
                            [key(atoms_of(x,ps,hs)) for x in integers]))
    return dict(version="released-1",primes=ps,heights=hs,slots=slots,
                original_unaries=phases[:len(base["pure"])],latest_phases=phases,
                observations=words,integers=list(map(str,integers)),exact_holes=[],
                best_phases=None,best_score=None,seed=97257,round=0,status="initial",
                parameters=dict(conflicts=12000,window=110,free_unaries=True,
                                backend="cadical195",probe_count=512))


def refit(state,ps,hs,slots,phases,rng, *, normalize=False):
    if normalize:
        from Dominance.dominance import cylinder_parent, phase_count
    unary=state["original_unaries"]
    # Enforce one switched unary on a core prime. Other unaries are free to move too.
    candidates=[i for i,s in enumerate(slots[:len(unary)]) if s[0][0]<3]
    forced=rng.choice(candidates)
    focused=state["observations"][-1]
    nonempty=[i for i in range(len(unary),len(slots)) if phases[i] is not None]
    near=[i for i in nonempty if sum(a!=b for a,b in
          zip(projection(focused,slots[i],ps,hs),phases[i]))==1]
    spare=[i for i,v in enumerate(phases) if v is None]
    selected=set(range(len(unary)))
    for group,count in [(near,25),(spare,32),(nonempty,22)]:
        selected.update(rng.sample(group,min(count,len(group))))
    more=[i for i in range(len(slots)) if i not in selected]
    selected.update(rng.sample(more,max(0,min(len(more),110-len(selected)))))
    movable=sorted(selected)
    fixed=[pack(s,v) for i,(s,v) in enumerate(zip(slots,phases)) if i not in selected and v is not None]
    needed=[w for w in state["observations"] if not any(matches(ps,hs,w,p) for p in fixed)]
    projected=[[projection(w,slots[i],ps,hs) for i in movable] for w in needed]
    pool=IDPool()
    with Solver(name="cadical195") as sat:
        choices=[]
        for k,i in enumerate(movable):
            menu={row[k] for row in projected}
            if phases[i] is not None:menu.add(tuple(phases[i]))
            if i==forced or (normalize and i<len(unary)):
                j,e=slots[i][0];p,h=ps[j],hs[j]
                limit=phase_count(p,h,e) if normalize else (p**e if e<=h else p**h*(p-1))
                menu.update((value,) for value in range(limit))
            if i==forced:
                menu.discard(tuple(unary[i]))
            if not menu:menu.add(None)
            lut={v:pool.id((i,v)) for v in sorted(menu,key=lambda x:() if x is None else x)}
            sat.append_formula(CardEnc.equals(list(lut.values()),1,vpool=pool).clauses)
            choices.append(lut)
        if normalize:
            # All unaries are movable and have full menus except the one forced inequality.
            unary_luts={tuple(slots[i][0]): lut for i,lut in zip(movable,choices) if i<len(unary)}
            for (j,e),lut in unary_luts.items():
                for (v,),literal in lut.items():
                    for d in range(1,e):
                        parent_lut=unary_luts.get((j,d),{})
                        ancestor=cylinder_parent(ps[j],hs[j],e,v,d)
                        parent=parent_lut.get((ancestor,))
                        if parent is not None:
                            sat.add_clause([-literal,-parent])
        for row in projected:
            sat.add_clause([lut[v] for lut,v in zip(choices,row) if v in lut])
        sat.set_phases([lut[tuple(phases[i])] for i,lut in zip(movable,choices)
                        if phases[i] is not None and tuple(phases[i]) in lut])
        sat.conf_budget(state["parameters"]["conflicts"])
        result=sat.solve_limited()
        if result is not True:return None,forced,("window_unsat" if result is False else "window_budget")
        yes=set(sat.get_model())
    new=list(phases)
    for i,lut in zip(movable,choices):new[i]=next(v for v,k in lut.items() if k in yes)
    return new,forced,"model_pending_check"


def main():
    p=ArgumentParser()
    p.add_argument("--base",default="Runs/rank24.json.gz")
    p.add_argument("--bank",default="Runs/integer_bank_final.json.gz")
    p.add_argument("--output",required=True,type=Path)
    p.add_argument("--rounds",type=int,default=80)
    p.add_argument("--seconds",type=float,default=90)
    a=p.parse_args()
    s=read(a.output) if a.output.exists() else initial(read(a.base),read(a.bank))
    if s["status"]=="box_cover":
        print("box_cover");return
    ps,hs,slots=s["primes"],s["heights"],s["slots"]
    alph=[list(product(range(p**h),range(1,p))) for p,h in zip(ps,hs)]
    points=Random(s["seed"])
    probes=[[points.choice(A) for A in alph] for _ in range(512)]
    write(a.output,s)
    start=monotonic()
    for i in range(a.rounds):
        if monotonic()-start>a.seconds:break
        if s["status"]!="model_pending_check":
            rng=Random(s["seed"]+s["round"])
            phases,forced,status=refit(s,ps,hs,slots,s["latest_phases"],rng)
            s.update(round=s["round"]+1,status=status,forced_slot=forced)
            if phases is None:
                write(a.output,s)
                continue
            s["latest_phases"]=phases
            write(a.output,s)
        phases=s["latest_phases"]
        pats=[pack(t,v) for t,v in zip(slots,phases) if v is not None]
        validate(ps,hs,pats)
        assert list(phases[s["forced_slot"]])!=s["original_unaries"][s["forced_slot"]]
        assert all(any(matches(ps,hs,w,p) for p in pats) for w in s["observations"])
        hole=exact_hole(alph,ps,hs,pats)
        if hole is None:
            s.update(status="box_cover",best_phases=phases,best_score=512);write(a.output,s);break
        word=[A[j] for A,j in zip(alph,hole)]
        assert not any(matches(ps,hs,word,p) for p in pats)
        x=str(actual_witness(word,ps,hs))
        s["observations"].append(word);s["exact_holes"].append(word)
        if x not in s["integers"]:s["integers"].append(x)
        s["status"]="exact_hole";write(a.output,s)
        score=sum(any(matches(ps,hs,w,p) for p in pats) for w in probes)
        if s["best_score"] is None or score>s["best_score"]:
            s.update(best_score=score,best_phases=phases)
        write(a.output,s)
    print(s["status"],s["round"],len(s["observations"]),len(s["exact_holes"]),s["best_score"])


if __name__=="__main__":main()
