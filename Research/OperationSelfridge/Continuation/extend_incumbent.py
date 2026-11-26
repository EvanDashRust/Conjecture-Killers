"""Append prime coordinates to a saved layout; verify its phase shapes and first hole."""
import argparse

from prefix_box import exact_hole, make_box
from prefix_incumbent import pack
from prefix_lift import validate
from prefix_sat import read, write


def extend(source, new_primes, new_heights):
    state = read(source)
    old = [pack(s,v) for s,v in zip(state["slots"],state["latest_phases"]) if v is not None]
    ps,hs = state["primes"]+new_primes, state["heights"]+new_heights
    alph,pure = make_box(ps,hs)
    validate(ps,hs,pure+old)
    hole = exact_hole(alph,ps,hs,old)
    if hole is None:
        raise ValueError("Extended incumbent already covers the box; verify separately.")
    return dict(primes=ps,heights=hs,pure=pure,patterns=old,
                uncovered_atom_word=[a[i] for a,i in zip(alph,hole)],
                source=str(source), added_coordinates=list(zip(new_primes,new_heights)))


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("source")
    p.add_argument("output")
    p.add_argument("coordinates",nargs="+",help="prime:height")
    a=p.parse_args()
    primes,heights=zip(*(map(int,x.split(":")) for x in a.coordinates))
    from pathlib import Path
    if Path(a.output).exists():
        p.error("Output exists.")
    write(Path(a.output),extend(a.source,list(primes),list(heights)))
