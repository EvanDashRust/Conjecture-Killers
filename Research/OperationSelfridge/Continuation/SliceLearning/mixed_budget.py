"""Verify a mixed-slot lower bound after arbitrary changes to every unary."""
import json
from pathlib import Path

from checkpoint import direct, patterns_for, phase, serial_digest


def shallow_count(p,h,axis):
    # At height zero the one unary mode fixes exactly one atom.
    if h == 0:
        return max(0,len(axis)-1)
    by_mode = []
    for e in range(1,h+2):
        lut = {}
        for j,atom in enumerate(axis):
            v = phase(p,h,atom,e)
            lut[v] = lut.get(v,0) | (1 << j)
        by_mode.append(lut)
    survivors = {(1 << len(axis))-1}
    for lut in by_mode:
        # Zero includes an omitted unary, or a phase missing this axis.
        survivors = {s & ~m for s in survivors for m in [0,*lut.values()]}
    return min(sum(bool(s & m) for m in by_mode[0].values()) for s in survivors)


def main():
    source = Path(__file__).with_name('mixed_products.json')
    for name,entry in json.loads(source.read_text()).items():
        ps,hs,pats = patterns_for(name)
        assert serial_digest(pats) == entry['pattern_sha256']
        box = entry['axes']
        direct(box,ps,hs,[p for p in pats if len(p)>1])
        t = [shallow_count(p,h,ax) for p,h,ax in zip(ps,hs,box)]
        assert t == entry['minimum_surviving_shallow_values']
        first,second = sorted(t)[:2]
        assert first*second == entry['minimum_mixed_edits']
        print(name,'all unary slots free, mixed edits at least',first*second,flush=True)


if __name__ == '__main__':
    main()
