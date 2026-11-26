"""Exact prefix-box CEGIS with portable atom words and atomic restart points."""
import argparse
import gzip
import hashlib
import json
import multiprocessing as mp
import os
from itertools import combinations, product
from pathlib import Path
from functools import lru_cache
from math import prod
import random
import signal
import tempfile
import shlex
from time import monotonic

from pysat.solvers import Solver
from prefix_box import exact_hole, make_box, odd_primes, value
from prefix_lift import crt, is_prime, matches, validate

VERSION = "prefix-cegis-2"
BACKEND = "cadical195"


def read(path):
    opener = gzip.open if str(path).endswith(".gz") else open
    with opener(path, "rt") as file:
        return json.load(file)


def write(path, state):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    raw = json.dumps(state, separators=(",", ":")).encode()
    if path.suffix == ".gz":
        raw = gzip.compress(raw, compresslevel=1, mtime=0)
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as file:
        try:
            file.write(raw)
            file.flush()
            os.fsync(file.fileno())
            file.close()
            os.replace(file.name, path)
            folder = os.open(path.parent, os.O_RDONLY)
            try:
                os.fsync(folder)
            finally:
                os.close(folder)
        finally:
            Path(file.name).unlink(missing_ok=True)


def atoms_of(x, primes, heights):
    atoms = []
    for p, h in zip(primes, heights):
        root = x % p**h
        tail = (x - root) // p**h
        while tail and tail % p == 0:
            tail //= p
        # x == root is covered by the auxiliary classes of the lift.
        atoms.append((root, tail % p if tail else 1))
    return atoms


def representative(atoms, primes, heights):
    _, x = crt([(p**(h+1), r+d*p**h) for p,h,(r,d) in zip(primes, heights, atoms)])
    assert atoms_of(x, primes, heights) == list(map(tuple, atoms))
    return x


@lru_cache(None)
def auxiliary_product(primes, heights):
    q=max([2,*primes,*(h+1 for h in heights)])+1
    result=1
    for n in range(sum(p**h for p,h in zip(primes,heights))):
        while not is_prime(q):
            q+=1
        result*=q
        q+=1
    return result


def actual_witness(word, primes, heights):
    """Escape the original per-root auxiliary lift with every auxiliary at -1."""
    auxiliary=auxiliary_product(tuple(primes),tuple(heights))
    _,x=crt([(auxiliary,auxiliary-1)]+[(p**(h+1),r+d*p**h)
             for p,h,(r,d) in zip(primes,heights,word)])
    assert key(atoms_of(x,primes,heights))==key(word)
    return x


def catalogue(config):
    primes, heights = config["primes"], config["heights"]
    if config["free_unaries"]:
        alphabets = [list(product(range(p**h), range(1,p))) for p,h in zip(primes,heights)]
        pure = []
    else:
        alphabets, pure = make_box(primes, heights)
    slots = [tuple(zip(subset, modes))
             for size in range(1 if config["free_unaries"] else 2, config["arity"]+1)
             for subset in combinations(range(len(primes)),size)
             for modes in product(*(range(1,heights[i]+2) for i in subset))]
    return alphabets, pure, slots


class Encoding:
    """A previously unseen phase gets one literal. A chain enforces at most one per slot."""

    def __init__(self, solver, slots, primes, heights):
        self.solver = solver
        self.slots = slots
        self.primes = primes
        self.heights = heights
        self.last = [0]*len(slots)
        self.labels = [{} for _ in slots]
        self.top = 0

    def fresh(self):
        self.top += 1
        return self.top

    def add(self, atoms):
        projections = {(i,e):value(p,h,atoms[i],e) for i,(p,h) in
                       enumerate(zip(self.primes,self.heights)) for e in range(1,h+2)}
        clause = []
        for s,slot in enumerate(self.slots):
            phase = tuple(projections[key] for key in slot)
            lut = self.labels[s]
            if phase not in lut:
                hit = self.fresh()
                lut[phase] = hit
                old = self.last[s]
                if old:
                    prefix = self.fresh()
                    for row in ((-old,-hit),(-old,prefix),(-hit,prefix)):
                        self.solver.add_clause(row)
                    self.last[s] = prefix
                else:
                    self.last[s] = hit
            clause.append(lut[phase])
        self.solver.add_clause(clause)

    def model(self, assignment, first):
        yes = {x for x in assignment if x>0}
        patterns = []
        for slot,lut in zip(self.slots,self.labels):
            default = tuple(first[key] for key in slot)
            phase = next((v for v,lit in lut.items() if lit in yes), default)
            patterns.append([[i,e,a] for (i,e),a in zip(slot,phase)])
        return patterns


def key(word):
    return tuple(map(tuple,word))


def start(args):
    source = read(args.input) if args.input else None
    primes = (list(map(int,args.primes.split(","))) if args.primes else
              source["primes"] if source else odd_primes(args.rank))
    heights = list(source["heights"]) if source else [0]*len(primes)
    if source and primes != source["primes"]:
        raise ValueError("Use --carry to translate a different catalogue.")
    for spec in args.depth:
        p,h = map(int,spec.split(":"))
        heights[primes.index(p)] = h
    if not primes or len(set(primes))!=len(primes) or any(p<=2 or not is_prime(p) for p in primes):
        raise ValueError("Expected distinct odd primes.")
    if min(heights)<0 or args.arity<1:
        raise ValueError("Invalid heights or arity.")
    cfg = dict(primes=primes,heights=heights,arity=args.arity,free_unaries=args.free_unaries,
               seed=args.seed,backend=BACKEND,encoding="observed-phase-sequential-amo",
               slot_rule="all subsets up to arity, all mode products; one phase per slot",
               atom_format="columns labelled by primes; each entry [low root, first nonzero digit]")
    alph,pure,slots = catalogue(cfg)
    state = dict(version=VERSION,config=cfg,pure=pure,slot_count=len(slots),observations=[],
                 exact_holes=[],integer_requirements=[],imports=[],completed=0,
                 timing={k:0.0 for k in ("encode","solve","hole","score")},
                 latest=None,best=None,best_score=None,pending=False,status="ready")
    def add(atoms):
        if not any(matches(primes,heights,atoms,pat) for pat in pure):
            state["observations"].append(atoms)
    add([a[0] for a in alph])
    integers = set(map(int,args.integer))
    if source:
        if source.get("terminal"):
            raise ValueError("Terminal catalogues need an explicit translation.")
        if source.get("uncovered_atom_word"):
            word = source["uncovered_atom_word"]
            if any(matches(source["primes"],source["heights"],word,pat)
                   for pat in source["pure"]+source["patterns"]):
                raise ValueError("Source witness is covered.")
            integers.add(actual_witness(word,source["primes"],source["heights"]))
            x = representative(word,source["primes"],source["heights"])
            add(atoms_of(x,primes,heights))
    for path in args.carry:
        old = read(path)
        if old["version"] != VERSION:
            raise ValueError("Unsupported source schema.")
        old_cfg = old["config"]
        for word in old["observations"]:
            x = representative(word,old_cfg["primes"],old_cfg["heights"])
            add(atoms_of(x,primes,heights))
        integers.update(map(int,old["integer_requirements"]))
        integers.update(actual_witness(w,old_cfg["primes"],old_cfg["heights"]) for w in old["exact_holes"])
        state["imports"].append({"name":Path(path).name,
                                 "sha256":hashlib.sha256(Path(path).read_bytes()).hexdigest(),
                                 "source_constraints":len(old["observations"])})
    for file in args.integer_file:
        integers.update(map(int,read(file)["integers"]))
    for x in sorted(integers):
        add(atoms_of(x,primes,heights))
    state["integer_requirements"] = list(map(str,sorted(integers)))
    state["observations"] = list(dict.fromkeys(map(key,state["observations"])))
    return state


def worker(path, rounds):
    state = read(path)
    cfg = state["config"]
    if state["version"] != VERSION or cfg["backend"] != BACKEND:
        raise ValueError("Checkpoint schema/backend mismatch.")
    primes,heights = cfg["primes"],cfg["heights"]
    alph,pure,slots = catalogue(cfg)
    if json.loads(json.dumps(pure)) != state["pure"] or len(slots)!=state["slot_count"]:
        raise ValueError("Checkpoint catalogue does not match its reconstruction.")
    indices = [{v:k for k,v in enumerate(a)} for a in alph]
    first = {(i,e):value(p,h,alph[i][0],e) for i,(p,h) in enumerate(zip(primes,heights))
             for e in range(1,h+2)}
    rng = random.Random(cfg["seed"])
    probes = [[rng.choice(a) for a in alph] for _ in range(64)]
    observations = {key(w) for w in state["observations"]}
    with Solver(name=BACKEND) as solver:
        enc = Encoding(solver, slots, primes, heights)
        t = monotonic()
        for word in state["observations"]:
            for i,atom in enumerate(word):
                indices[i][tuple(atom)]
            enc.add(word)
        if state["latest"]:
            saved=[tuple(a for i,e,a in p) for p in state["latest"]]
            solver.set_phases([lut[v] for lut,v in zip(enc.labels,saved) if v in lut])
        state["timing"]["encode"] += monotonic()-t
        for _ in range(rounds):
            if not state["pending"]:
                t = monotonic()
                sat = solver.solve()
                state["timing"]["solve"] += monotonic()-t
                if not sat:
                    state["status"] = "unsat_finite_constraints"
                    write(path,state)
                    return
                state["latest"] = enc.model(solver.get_model(),first)
                state["pending"] = True
                state["status"] = "model_pending_hole_check"
                write(path,state)
            patterns = state["latest"]
            t = monotonic()
            hole = exact_hole(alph,primes,heights,patterns)
            state["timing"]["hole"] += monotonic()-t
            if hole is None:
                state.update(status="box_cover", pending=False, best=patterns,best_score=len(probes))
                write(path,state)
                return
            point = tuple(alph[i][j] for i,j in enumerate(hole))
            assert point not in observations
            assert not any(matches(primes,heights,point,p) for p in patterns+list(pure))
            axis = state["completed"] % len(primes)
            batch = [point[:axis]+(a,)+point[axis+1:] for a in alph[axis]]
            added = [w for w in batch if w not in observations]
            observations.update(added)
            state["observations"].extend(added)
            state["exact_holes"].append(point)
            x=str(actual_witness(point,primes,heights))
            if x not in state["integer_requirements"]:
                state["integer_requirements"].append(x)
            state["completed"] += 1
            state.update(pending=False,status="bounded_incomplete")
            # Commit the exact witness before either scoring or encoding can be interrupted.
            write(path,state)
            t = monotonic()
            score = sum(any(matches(primes,heights,w,p) for p in patterns) for w in probes)
            if state["best_score"] is None or score>state["best_score"]:
                state.update(best=patterns,best_score=score)
            state["timing"]["score"] += monotonic()-t
            t = monotonic()
            for word in added:
                enc.add(word)
            state["timing"]["encode"] += monotonic()-t
        write(path,state)


def main():
    p=argparse.ArgumentParser()
    p.add_argument("--resume")
    p.add_argument("--output")
    p.add_argument("--carry",action="append",default=[])
    p.add_argument("--integer-file",action="append",default=[])
    p.add_argument("--integer",action="append",default=[])
    p.add_argument("--input")
    p.add_argument("--rank",type=int,default=8)
    p.add_argument("--primes")
    p.add_argument("--depth",action="append",default=[])
    p.add_argument("--arity",type=int,default=3)
    p.add_argument("--rounds",type=int,default=100)
    p.add_argument("--seconds",type=float,default=40)
    p.add_argument("--seed",type=int,default=2707)
    p.add_argument("--free-unaries",action="store_true")
    args=p.parse_args()
    if args.seconds<=0 or args.rounds<0:
        p.error("Pass a positive time limit and nonnegative round budget.")
    path=Path(args.resume or args.output or "prefix_sat_result.json")
    if args.resume:
        import sys
        allowed={"--resume","--rounds","--seconds"}
        if any(s.split("=")[0] not in allowed for s in sys.argv[1:] if s.startswith("--")):
            p.error("Resume takes only --rounds and --seconds. Use --carry for a changed catalogue.")
        state=read(path)
    else:
        if path.exists():
            p.error("Existing checkpoint. Use --resume or a fresh --output.")
        state=start(args)
    if state["status"] in ("box_cover","unsat_finite_constraints") and args.resume:
        print(state["status"])
        return
    state["run_limits"]={"seconds":args.seconds,"rounds":args.rounds}
    state["resume_command"]="python3 prefix_sat.py --resume " + shlex.quote(str(path))
    write(path,state)
    child=mp.Process(target=worker,args=(path,args.rounds))
    child.start()
    reason=None
    def interrupt(signum, frame):
        raise KeyboardInterrupt
    old=signal.signal(signal.SIGTERM,interrupt)
    try:
        child.join(args.seconds)
        if child.is_alive():
            reason="timeout"
    except KeyboardInterrupt:
        reason="interrupted"
    finally:
        if child.is_alive():
            child.kill()
            child.join()
        signal.signal(signal.SIGTERM,old)
    state=read(path)
    if reason and state["status"] not in ("box_cover","unsat_finite_constraints"):
        state["status"]=reason
        write(path,state)
    elif child.exitcode and not reason:
        raise RuntimeError(f"Worker exited with {child.exitcode}; checkpoint retained")
    print(json.dumps({k:state[k] for k in ("status","completed","slot_count","timing","best_score")}
                     |{"constraints":len(state["observations"])}),flush=True)


if __name__=="__main__":
    main()
