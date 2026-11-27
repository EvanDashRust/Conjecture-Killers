"""Cumulative coordinated phase repair on a high-dimensional prefix catalogue."""
import argparse
from collections import Counter
from itertools import combinations, product
from math import prod
from pathlib import Path
import random
from time import monotonic

from pysat.card import CardEnc
from pysat.examples.rc2 import RC2
from pysat.formula import IDPool,WCNF
from prefix_box import exact_hole, make_box, value
from prefix_lift import matches,validate,crt
from prefix_sat import actual_witness, atoms_of, key, read, representative, write


def shape(pattern):
    return tuple((i,e) for i,e,a in pattern)


def projection(word,slot,ps,hs):
    return tuple(value(ps[i],hs[i],word[i],e) for i,e in slot)


def pack(slot,phase):
    return [[i,e,v] for (i,e),v in zip(slot,phase)]


def prepare(base,additional):
    ps,hs=base["primes"],base["heights"]
    alph,pure=make_box(ps,hs)
    original=base["patterns"]
    occupied={shape(p) for p in pure+original}
    density={(i,e):max(Counter(value(p,h,a,e) for a in alph[i]).values())/len(alph[i])
             for i,(p,h) in enumerate(zip(ps,hs)) for e in range(1,h+2)}
    reserve=[]
    for k in (2,3,4):
        for subset in combinations(range(len(ps)),k):
            for modes in product(*(range(1,hs[i]+2) for i in subset)):
                slot=tuple(zip(subset,modes))
                if slot not in occupied:
                    reserve.append((-prod(density[t] for t in slot),slot))
    slots=[shape(p) for p in original]+[s for _,s in sorted(reserve)[:additional]]
    phases=[tuple(a for i,e,a in p) for p in original]+[None]*min(additional,len(reserve))
    return slots,phases


def refit(ps,hs,slots,phases,words,movable,probes):
    lookup={s:k for k,s in enumerate(movable)}
    fixed=[pack(s,v) for j,(s,v) in enumerate(zip(slots,phases)) if j not in lookup and v is not None]
    need=[w for w in words if not any(matches(ps,hs,w,p) for p in fixed)]
    formula=WCNF()
    pool=IDPool()
    projected=[[projection(w,slots[j],ps,hs) for j in movable] for w in need]
    options=[]
    for k,j in enumerate(movable):
        old=phases[j]
        menu={v[k] for v in projected}|{old}
        lut={v:pool.id((k,v)) for v in sorted(menu,key=lambda v:() if v is None else v)}
        formula.extend(CardEnc.equals(list(lut.values()),1,vpool=pool).clauses)
        # Existing phases with greater measured exclusive coverage cost more to move.
        formula.append([lut[old]],weight=1+probes.get(j,0))
        options.append(lut)
    for v in projected:
        formula.append([lut[q] for lut,q in zip(options,v)])
    with RC2(formula) as solver:
        model=solver.compute()
    if model is None:return None
    yes=set(model)
    new=list(phases)
    for j,lut in zip(movable,options):
        new[j]=next(v for v,lit in lut.items() if lit in yes)
    return new


def run(a):
    base=read(a.input)
    if base.get("terminal"):raise ValueError("Only full untargeted boxes are supported.")
    ps,hs=base["primes"],base["heights"]
    alph,pure=make_box(ps,hs)
    assert list(map(key,pure))==list(map(key,base["pure"]))
    out=Path(a.output)
    if out.exists():
        state=read(out)
        assert ps==state["primes"] and hs==state["heights"] and a.seed==state["seed"]
        slots=[tuple(map(tuple,s)) for s in state["slots"]]
        phases=[None if v is None else tuple(v) for v in state["latest_phases"]]
    else:
        slots,phases=prepare(base,a.reserve)
        state=dict(version="incumbent-1",primes=ps,heights=hs,pure=pure,slots=slots,seed=a.seed,
                   parameters=dict(window=40,holdout=1024,reserve=a.reserve,solver="RC2/glucose3"),
                   latest_phases=phases,best_phases=phases,best_misses=None,
                   atom_format="one [low root, first exit digit] per labelled prime column",
                   exact_holes=[],observations=[base["uncovered_atom_word"]],integers=[],round=0,
                   timing=dict(refit=0.,hole=0.,validation=0.),width=40)
    incoming=list(map(int,a.integer))
    for file in a.integer_file:
        incoming.extend(map(int,read(file)["integers"]))
    state["integers"]=list(dict.fromkeys(state["integers"]+list(map(str,incoming))))
    words=dict.fromkeys(map(key,state["observations"]))
    for path in a.words:
        src=read(path)
        from hashlib import sha256
        stamp=sha256(Path(path).read_bytes()).hexdigest()
        state.setdefault("imports",{})[stamp]=Path(path).name
        old_ps=[z["prime"] for z in src["coordinates"]]
        old_hs=[z["height"] for z in src["coordinates"]]
        for word in src["atom_words"]:
            x=representative(word,old_ps,old_hs)
            w=key(atoms_of(x,ps,hs))
            if not any(matches(ps,hs,w,p) for p in pure): words[w]=None
    for x in state["integers"]:
        w=key(atoms_of(int(x),ps,hs))
        if not any(matches(ps,hs,w,p) for p in pure):
            words[w]=None
    state["observations"]=list(words)
    rng=random.Random(a.seed)
    test=[[rng.choice(A) for A in alph] for _ in range(1024)]
    start=monotonic()
    for _ in range(a.rounds):
        if monotonic()-start>=a.seconds: break
        step=state["round"]
        rng=random.Random(a.seed+step+1)
        pool=list(range(len(slots)))
        width=state["width"]
        # Alternate near misses, unassigned reserve slots, and arbitrary assigned slots.
        focus=state["observations"][-1]
        near=[j for j,v in enumerate(phases) if v is not None and
              sum(x!=y for x,y in zip(v,projection(focus,slots[j],ps,hs)))==1]
        fresh=[j for j,v in enumerate(phases) if v is None]
        selected=set(rng.sample(near,min(len(near),width//3)))
        selected.update(rng.sample(fresh,min(len(fresh),width//3)))
        others=[j for j in pool if j not in selected]
        selected.update(rng.sample(others,min(len(others),width-len(selected))))
        t=monotonic()
        penalties={j:sum(matches(ps,hs,w,pack(slots[j],phases[j])) for w in test)
                   for j in selected if phases[j] is not None}
        proposal=refit(ps,hs,slots,phases,state["observations"],sorted(selected),penalties)
        state["timing"]["refit"]+=monotonic()-t
        state["round"]+=1
        if proposal is None:
            state["status"]="window_unsat" if width<len(slots) else "unsat_finite_constraints"
            state["width"]=min(2*width,len(slots))
            write(out,state)
            if width==len(slots):break
            continue
        phases=proposal
        patterns=[pack(s,v) for s,v in zip(slots,phases) if v is not None]
        validate(ps,hs,list(pure)+patterns)
        assert all(any(matches(ps,hs,w,p) for p in patterns) for w in state["observations"])
        state.update(latest_phases=phases,status="model_pending_check",width=40)
        write(out,state)
        t=monotonic()
        hole=exact_hole(alph,ps,hs,patterns)
        state["timing"]["hole"]+=monotonic()-t
        if hole is None:
            state.update(status="box_cover",best_phases=phases,best_misses=0)
            write(out,state)
            break
        w=[A[j] for A,j in zip(alph,hole)]
        assert not any(matches(ps,hs,w,p) for p in patterns+list(pure))
        state["exact_holes"].append(w)
        number=str(actual_witness(w,ps,hs))
        if number not in state["integers"]:
            state["integers"].append(number)
        state["observations"].append(w)
        state["status"]="exact_hole"
        write(out,state)
        t=monotonic()
        miss=sum(not any(matches(ps,hs,w,p) for p in patterns) for w in test)
        if state["best_misses"] is None or miss<state["best_misses"]:
            state.update(best_misses=miss,best_phases=phases)
        state["timing"]["validation"]+=monotonic()-t
        write(out,state)
    print(state["status"],state["round"],len(state["observations"]),state["best_misses"],flush=True)


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--input",default=str(Path(__file__).with_name("prefix_candidate.json")))
    p.add_argument("--output",required=True)
    p.add_argument("--reserve",type=int,default=400)
    p.add_argument("--seed",type=int,default=2607)
    p.add_argument("--rounds",type=int,default=60)
    p.add_argument("--seconds",type=int,default=120)
    p.add_argument("--words",action="append",default=[])
    p.add_argument("--integer-file",action="append",default=[])
    p.add_argument("--integer",action="append",default=[])
    run(p.parse_args())
