"""Independent atom-set checks of every relocation in the rank-24 delta archive."""
import gzip
import hashlib
from itertools import product
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "Review"))
from check_original import concrete_hole


def load(path):
    return json.loads(gzip.decompress(path.read_bytes()))


def check():
    source_file = ROOT / "Runs" / "released24.json.gz"
    source = load(source_file)
    rep = load(ROOT / "Dominance" / "repairs.json.gz")
    assert rep["source_sha256"] == hashlib.sha256(source_file.read_bytes()).hexdigest()
    bank = load(ROOT / "Runs" / "integer_bank_latest.json.gz")
    assert set(bank["integers"]) == set(source["integers"])
    ps, hs, slots = source["primes"], source["heights"], source["slots"]
    assert len(slots) == 3303 and len(source["exact_holes"]) == 90
    alph = [tuple(product(range(p**h), range(1, p))) for p, h in zip(ps, hs)]
    def project(i, e, atom):
        r,d = atom
        return r % ps[i]**e if e <= hs[i] else r*(ps[i]-1)+d-1
    incidences = {(i, e, v): {a for a in axis if project(i,e,a)==v}
                  for i, axis in enumerate(alph) for e in range(1, hs[i]+2)
                  for v in {project(i,e,a) for a in axis}}
    def unary_union(phases, i, except_id=None, before=None):
        return set().union(*(incidences[i, e, value[0]] for j, (slot, value)
                             in enumerate(zip(slots, phases)) if value is not None and
                             j != except_id and len(slot) == 1 for coord,e in slot
                             if coord == i and (before is None or e < before)))
    for row in rep["records"]:
        step = row["step"]
        if step == "original":
            phase = source[row["base"]].copy()
        for j, old, new in row["changes"]:
            slot = slots[j]
            if step == "unary":
                old, new = [old], [new]
                coord,e = slot[0]
                shallower = unary_union(phase, coord, except_id=j, before=e)
                assert incidences[coord,e,old[0]] <= shallower
                assert not (incidences[coord,e,new[0]] & shallower)
            else:
                assert len(slot)>1
                # A rectangle is contained in the union of the coordinate slabs
                # iff at least one coordinate projection lies within those slabs.
                assert any(incidences[c,e,v] <= unary_union(phase,c)
                           for (c,e),v in zip(slot,old))
                assert all(incidences[c,e,v] - unary_union(phase,c)
                           for (c,e),v in zip(slot,new))
            assert phase[j] == old
            phase[j] = new
        pats = [[(c,e,v) for (c,e),v in zip(slot, val)] for slot,val in zip(slots, phase)
                if val is not None]
        data = dict(primes=ps,heights=hs,pure=[],patterns=pats,uncovered_atom_word=row["word"])
        x,copies = concrete_hole(data)
        assert str(x)==row["integer"]
        if row["base"]=="latest_phases" and step=="original":
            assert copies==32536723404
        print(row["base"], step, "moves", len(row["changes"]), "checked integer",x,
              "generator classes",copies)


if __name__=="__main__":
    check()
