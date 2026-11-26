"""Phase-specific seven-product bound with freely rephased unary slots."""
import json
from fractions import Fraction as F
from itertools import combinations, product
from math import lcm
from pathlib import Path

from checkpoint import direct, patterns_for, phase


def denominators(p,h,axis):
    if h == 0:
        assert len(axis) >= 2
        return {d-1:len(axis)-1 for _,d in axis}
    masks = []
    for e in range(1,h+2):
        groups = {}
        for j,atom in enumerate(axis):
            v=phase(p,h,atom,e)
            groups[v]=groups.get(v,0)|(1<<j)
        masks.append(groups)
    survivors = {(1<<len(axis))-1}
    for level in masks:
        survivors = {s & ~m for s in survivors for m in [0,*level.values()]}
    assert 0 not in survivors
    ans = {}
    for s in survivors:
        present = [v for v,mask in masks[0].items() if s & mask]
        for v in present:
            ans[v]=min(ans.get(v,len(present)),len(present))
    return ans


def main():
    ps,hs,pats=patterns_for('scored_mixed')
    rows=json.loads(Path(__file__).with_name('mixed_phase_mixture.json').read_text())
    tables=[]
    count=[]
    for n,box in rows:
        direct(box,ps,hs,[p for p in pats if len(p)>1])
        assert isinstance(n,int) and n>0
        count.append(n)
        tables.append([denominators(p,h,axis) for p,h,axis in zip(ps,hs,box)])
    scale=lcm(*(d for row in tables for ax in row for d in ax.values()))
    possible=[]
    for i,p in enumerate(ps):
        labels=sorted(set().union(*(b[i] for b in tables)))
        possible.append([[scale//b[i][v] if v in b[i] else 0 for b in tables] for v in labels])
    peak=max(sum(n*x*y for n,x,y in zip(count,left,right))
             for A,B in combinations(possible,2) for left,right in product(A,B))
    bound=F(peak,sum(count)*scale**2)
    print('scored mixed maximum single mixed phase mass',bound,
          'all-unaries-free mixed edits at least',-(-bound.denominator//bound.numerator))
    assert bound == F(2,9)


if __name__=='__main__':
    main()
