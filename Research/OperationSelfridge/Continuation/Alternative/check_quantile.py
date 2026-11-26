"""Independent finite cross-check of the orbit-2 quantile kernel for 23 absent."""
from fractions import Fraction as Q
from pathlib import Path
from itertools import product
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "TheoryJoint"))
from orbit_quantile import head


def pmf(p):
    # i represents min(1 + T,10), where P(T>=k)=1/p**k.
    return [Q(p-1, p**j) for j in range(1,10)]+[Q(1,p**9)]


def main():
    s,u,adjusted_mean,third,retained = head(2,Q(1,4))
    assert s==Q(45,68) and u==Q(4,3)
    cells = [i for i in range(45) if i%3!=0 and i%5!=0 and i%9!=2 and i%15!=1]
    n=len(cells)
    assert n==17
    groups=[]
    for q in (1,3,9,5,15,45):
        masks={}
        for i,x in enumerate(cells):
            masks[x%q]=masks.get(x%q,0) | 1<<i
        groups.append(masks.values())
    maximum=tuple(max(mask.bit_count() for mask in group) for group in groups)
    # Direct complement deficits. Drop duplicates to speed the exhaustive check.
    deficits=set()
    for subset in range(1<<n):
        complement=((1<<n)-1)^subset
        penalty=tuple(m-max((mask&complement).bit_count() for mask in group)
                      for m,group in zip(maximum,groups))
        deficits.add((subset.bit_count(),penalty))
    p3,p5=pmf(3),pmf(5)
    rows=[]
    for a,b in product(range(1,11),repeat=2):
        weights=(1,1,a,b,b,a*b)
        by_size=[10**8]*(n+1)
        for k,penalty in deficits:
            by_size[k]=min(by_size[k],sum(w*d for w,d in zip(weights,penalty)))
        rows.append((p3[a-1]*p5[b-1],by_size))
    true_mean=sum(Q(x,n)*y for x,y in zip(maximum,
                  (Q(1),Q(1),Q(3,2),Q(5,4),Q(5,4),Q(15,8))))
    for t in [Q(0), Q(9,10), Q(1),Q(11,10),u,Q(3,2),Q(2),Q(3),Q(7,2),Q(23,3),
              Q(19),Q(75),Q(417),Q(54000)]:
        v=max(t,u)
        correction=sum(prob*max(k*v-losses[k] for k in range(n+1))/n
                       for prob,losses in rows)
        direct = true_mean-v+correction+s*(v-t)
        stored=adjusted_mean-s*t+sum(mass*max(t-a,0) for a,mass in retained)
        assert direct==stored,(t,direct,stored)
    print("Orbit r=2, no 23. Direct subset deficit envelope matches retained quantile")
    print("at 14 thresholds, for all 100 capped 3/5 exponent pairs and all 131072 cell subsets.")
    print("head mass",s,"quantile",u,"upper-tail mean input",adjusted_mean,"unconditional cubic",third)


if __name__ == '__main__':
    main()
