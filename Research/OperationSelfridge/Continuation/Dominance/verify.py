"""Standard-library replay of pointwise dominance, learned cuts, and CRT escapes."""
from hashlib import sha256
import gzip
from itertools import product
import json
from math import prod
from pathlib import Path
import sys

BASE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(BASE / "Review"))
from check_original import canonical_schematic, concrete_hole
from unary_orbits import canonicalize, switch_orbit


def load(path):
    with gzip.open(path, "rt") as f:
        return json.load(f)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def key(word):
    return tuple(map(tuple, word))


def value(p, h, pair, mode):
    r, d = pair
    return r * (p-1) + d-1 if mode == h+1 else r % p**mode


def masks(ps, hs, patterns):
    """Full alphabets map actual coordinate atoms to accepting pattern bitsets."""
    axes = [list(product(range(p**h), range(1,p))) for p,h in zip(ps,hs)]
    all_bits = (1 << len(patterns)) - 1
    out = [{atom: all_bits for atom in axis} for axis in axes]
    for i, pat in enumerate(patterns):
        for c, mode, label in pat:
            for atom in axes[c]:
                if value(ps[c], hs[c], atom, mode) != label:
                    out[c][atom] ^= 1 << i
    return out, all_bits


def matching(bits, universe, word):
    for dictionary, atom in zip(bits, word, strict=True):
        universe &= dictionary[tuple(atom)]
    return universe


def patterns(slots, phases):
    assert len(slots) == len(phases)
    return [[(c,e,v) for (c,e),v in zip(slot, phase, strict=True)]
            for slot, phase in zip(slots, phases) if phase is not None]


def unary_atoms(ps, hs, slots, phases):
    covered = [set() for p in ps]
    for slot, phase in zip(slots, phases):
        if len(slot) == 1:
            (c, e), = slot
            p,h = ps[c], hs[c]
            covered[c].update((r,d) for r,d in product(range(p**h),range(1,p))
                              if value(p,h,(r,d),e)==phase[0])
    return covered


def certify_integer(ps,hs,pats,word,expected=None):
    x, copies = concrete_hole(dict(primes=ps, heights=hs, pure=[], patterns=pats, uncovered_atom_word=word))
    if expected is not None:
        assert str(x)==expected
    return str(x), copies


def main():
    orig_path = BASE/"Runs/released24.json.gz"
    repair_path = BASE/"Dominance/repairs.json.gz"
    src = load(orig_path)
    rep = load(repair_path)
    assert digest(orig_path) == rep["source_sha256"]
    bank=load(BASE/"Runs/integer_bank_latest.json.gz")
    assert set(bank["integers"]) <= set(src["integers"])
    ps, hs, slots = src["primes"], src["heights"], src["slots"]
    assert (ps,hs) == (rep["primes"],rep["heights"])
    assert len({tuple(map(tuple,s)) for s in slots}) == len(slots)
    recovered = {}
    saved_words = set(map(key,src["observations"]))
    saved_ints = set(src["integers"])
    for rec in rep["records"]:
        base = rec["base"]
        phases = recovered.setdefault(base, list(src[base]))
        for i, old, new in rec["changes"]:
            slot=slots[i]
            if rec["step"]=="unary":
                (c,e),=slot
                p,h=ps[c],hs[c]
                assert phases[i]==[old]
                covered=set()
                for t,v in zip(slots,phases):
                    if len(t)==1 and t[0][0]==c and t[0][1]<e:
                        covered.update(atom for atom in product(range(p**h),range(1,p))
                                       if value(p,h,atom,t[0][1])==v[0])
                slab=lambda a: {atom for atom in product(range(p**h),range(1,p)) if value(p,h,atom,e)==a}
                assert slab(old) <= covered and slab(new) and not (slab(new) & covered)
                phases[i]=[new]
            else:
                assert rec["step"]=="mixed" and phases[i]==old and len(slot)>1
                if i==rec["changes"][0][0]:
                    unary=unary_atoms(ps,hs,slots,phases)
                def live(lit,a):
                    c,e=lit
                    return any(value(ps[c],hs[c],atom,e)==a and atom not in unary[c]
                               for atom in product(range(ps[c]**hs[c]),range(1,ps[c])))
                assert not all(live(t,a) for t,a in zip(slot,old))
                assert all(live(t,a) for t,a in zip(slot,new))
                phases[i]=new
        pats=patterns(slots,phases)
        bits,all_bits=masks(ps,hs,pats)
        missed=sum(not matching(bits,all_bits,w) for w in src["observations"])
        assert missed==rec["missed_original"]
        x,copies=certify_integer(ps,hs,pats,rec["word"],rec["integer"])
        saved_words.add(key(rec["word"]));saved_ints.add(x)
        print(base,rec["step"],"old misses",missed,"lifted classes",copies,"exact integer",x)
    assert saved_words==set(map(key,rep["observations"])) and saved_ints==set(rep["integers"])
    auxiliary=prod(canonical_schematic(ps,hs,[]).values())
    for name in ("search","challenger","sibling"):
        path=BASE/f"Dominance/{name}.json.gz"
        state=load(path)
        assert (ps,hs,slots)==(state["primes"],state["heights"],state["slots"])
        assert digest(orig_path)==state["source_sha256"] and digest(repair_path)==state["repairs_sha256"]
        if "extra_sha256" in state:
            previous = "search" if name=="challenger" else "challenger"
            old_path=BASE/f"Dominance/{previous}.json.gz"
            assert state["extra_sha256"]==digest(old_path)
            older=load(old_path)
            assert state["inherited_products"]==older.get("inherited_products",[])+[r["product"] for r in older["proposals"]]
        phases=list(recovered[state["start_base"]])
        if "canonical_orbit" in state:
            phases = switch_orbit(ps, hs, slots, phases, state["canonical_orbit"])
        old_boxes=[]
        for rec in state["proposals"]:
            j=rec["round"]
            for i,old,new in rec["changes"]:
                assert phases[i]==old
                phases[i]=new
            # Verify the non-overlap invariant even on proposals whose small unaries moved.
            for c,(p,h) in enumerate(zip(ps,hs)):
                pure=[(slot[0][1],v[0]) for slot,v in zip(slots,phases) if len(slot)==1 and slot[0][0]==c]
                assert all(sum(value(p,h,atom,e)==v for e,v in pure)<=1
                           for atom in product(range(p**h),range(1,p)))
            if "canonical_orbit" in state:
                orbit, canonical, _ = canonicalize(ps,hs,slots,phases)
                assert orbit==state["canonical_orbit"] and phases==canonical
            if rec.get("sat_status")=="model_pending_check":
                i=rec["forced_slot"]
                assert phases[i]!=src["original_unaries"][i]
            pats=patterns(slots,phases)
            bits,all_bits=masks(ps,hs,pats)
            missed=sum(not matching(bits,all_bits,w) for w in saved_words)
            assert missed==rec["missed_constraints"]
            box=[set(map(tuple,axis)) for axis in rec["product"]]
            assert prod(map(len,box))==int(rec["product_size"])
            # A product intersects a pattern iff each of its literal slabs intersects the corresponding axis.
            for pat in pats:
                assert any(all(value(ps[c],hs[c],a,e)!=v for a in box[c]) for c,e,v in pat)
            word=key(rec["word"])
            source=old_boxes[rec["separated_product"]] if "separated_product" in rec else None
            if "separated_inherited_product" in rec:
                source=state["inherited_products"][rec["separated_inherited_product"]]
            if source is not None:
                assert all(w in map(tuple,axis) for w,axis in zip(word,source,strict=True))
            x,copies=certify_integer(ps,hs,pats,word)
            assert x in state["integers"]
            # CRT witnesses use the canonical representative with every auxiliary coordinate −1.
            moduli=[p**(h+1) for p,h in zip(ps,hs)]+[auxiliary]
            period=prod(moduli)
            basis=[(period//m)*pow(period//m,-1,m) for m in moduli]
            for point in rec["batch"]:
                assert all(tuple(a) in axis for a,axis in zip(point,box,strict=True))
                residues=[r+d*p**h for (r,d),p,h in zip(point,ps,hs)]+[auxiliary-1]
                saved_ints.add(str(sum(a*b for a,b in zip(residues,basis))%period))
                saved_words.add(key(point))
            assert word in set(map(key,rec["batch"]))
            old_boxes.append(rec["product"])
            print(name,j,"old misses",missed,"batch",len(rec["batch"]),"atoms in product",rec["product_size"],"lifted classes",copies)
        assert phases==state["latest_phases"]
        assert saved_words==set(map(key,state["observations"])) and saved_ints==set(state["integers"])
        print(name,"bank",len(saved_words),"labelled points",len(saved_ints),"integers")


if __name__=="__main__":
    main()
