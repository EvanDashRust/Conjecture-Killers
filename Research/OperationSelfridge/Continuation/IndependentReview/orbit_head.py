"""Recompute the capped head hinge via the active-line ties, without hull construction."""
from collections import Counter
from fractions import Fraction as F
from functools import cache
from itertools import combinations, product
from math import prod
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "TheoryJoint"))
from orbit_quantile import head, CASES


@cache
def direct_law(orbit):
    cells = [(a,b) for a,b in product(range(9),range(5))
             if a % 3 != 0 and b != 0 and a != orbit and (a % 3,b) != (1,1)]
    n = len(cells)
    assert n == (17 if orbit==2 else 18)
    # The low-phase multiplicities are the six coordinate partitions.
    def key(a,b):
        return (0, a%3, a, b, (a%3,b), (a,b))
    keys = [key(a,b) for a,b in cells]
    rows = [set() for _ in range(n+1)]
    rows[0].add((0,)*6)
    for k in range(1,n+1):
        for chosen in combinations(keys,k):
            rows[k].add(tuple(max(Counter(col).values()) for col in zip(*chosen)))
    (all_counts,) = rows[n]
    def raw(q,j):
        x = F(1,q)
        return [1,1/(1-x),(1+x)/(1-x)**2,(1+4*x+x*x)/(1-x)**3][j]
    exps = [(0,0),(0,0),(1,0),(0,1),(0,1),(1,1)]
    mean = sum(F(c,n)*raw(3,a)*raw(5,b) for c,(a,b) in zip(all_counts,exps))
    third = sum(F(min(all_counts[i],all_counts[j],all_counts[k]),n)
                *prod(raw(q,exps[i][c]+exps[j][c]+exps[k][c]) for c,q in enumerate((3,5)))
                for i,j,k in product(range(6), repeat=3))
    law = Counter()
    def cap(q,k):
        return F(q-1,q**k) if k<10 else F(1,q**9)
    for a,b in product(range(1,11),repeat=2):
        weights = [1,1,a,b,b,a*b]
        highs = [max(sum(u*v for u,v in zip(row,weights)) for row in R) for R in rows]
        # Lower hinge numerator on an n-point space is max_k[k*x-deficit[k]].
        deficits = [highs[n]-highs[n-k] for k in range(n+1)]
        points = {F(v-u,j-i) for i,u in enumerate(deficits)
                  for j,v in enumerate(deficits) if i<j and v>=u}
        for x in points:
            a0,b0=x.as_integer_ratio()
            vals=[i*a0-b0*d for i,d in enumerate(deficits)]
            top=max(vals)
            k=[i for i,v in enumerate(vals) if v==top]
            jump=max(k)-min(k)
            if jump:
                law[x]+=F(jump,n)*cap(3,a)*cap(5,b)
    assert sum(law.values()) == 1
    return n, mean, third, law


def direct_head(orbit,density):
    n, mean, third, law = direct_law(orbit)
    s = density*45/n
    keep = s
    tail = {}
    for x in sorted(law,reverse=True):
        take=min(keep,law[x])
        if take:
            tail[x]=take
            keep-=take
    t = min(tail)
    correction=sum(max(t-x,0)*w for x,w in law.items())
    return s, t, mean + correction -(1-s)*t, third, sorted(tail.items())


if __name__=="__main__":
    for name in ("no23","no29","no31","no37","head1","head2"):
        orbit,_,density,_ = CASES[name]
        result = direct_head(orbit,density)
        ref = head(orbit,density)
        assert result[:4] == ref[:4] and result[4] == [(x,w) for x,w in ref[4] if w]
        print(name, "independent active-line calculation agrees, mean",result[2],
              "third moment",result[3],"retained breakpoints",len(result[4]),flush=True)
