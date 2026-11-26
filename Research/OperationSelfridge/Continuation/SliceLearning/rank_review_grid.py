"""Evaluate the orbit-2 finite-rank argument on its exact fractional state grid."""
import json
from fractions import Fraction as F
from math import isqrt
from pathlib import Path

from rank_review import UNIT, ceil, quantile_law


def upper(primes, cuts, grid):
    edge=max(cuts)+grid
    v=[0]*(edge+1)
    a=b=0
    for p,t in reversed(list(zip(primes,cuts))):
        r=p-1
        assert 0<=2*t<=r*grid
        out=[0]
        cden=grid*r-t
        for m in range(1,edge+1):
            # The input value is m/grid and the threshold is t/grid.
            stop=max(2,edge//m+1)
            tail=ceil(a*m*(r*stop+1)-b*r*grid,r*grid)
            for j in reversed(range(2,stop)):
                tail=ceil(r*v[m*j]+tail,p)
            base=v[m]
            kden=grid*r-min(m,t)
            change=grid*r*(tail-base)
            first=ceil(change,p*kden)
            second=ceil(change*kden-UNIT*(kden-cden)*p*cden,p*cden*kden)
            charge=ceil(UNIT*max(m-t,0),cden)
            out.append(base+max(first,second)+charge)
        a=ceil(a*(cden+grid)+UNIT*grid,cden)
        b+=UNIT*t//cden
        v=out
    return edge,v,a,b


def main():
    cert=json.loads(Path(__file__).with_name('rank_review_grid.json').read_text())
    grid=cert['grid']
    cuts=cert['threshold_numerators']
    assert grid == 6 and len(cuts)+2 == 74
    primes=[q for q in range(11,5000) if all(q%d for d in range(2,isqrt(q)+1))][:len(cuts)]
    assert len(primes)==len(cuts)
    law,slack=quantile_law()
    edge,v,a,b=upper(primes,cuts,grid)
    charge=1-sum(law.values())+slack*F(a,UNIT)
    for x,w in law.items():
        m=x*grid
        assert m.denominator==1
        charge+=w*F(v[int(m)] if m<=edge else a*x-b,UNIT)
    numerator=ceil(charge.numerator*10**12,charge.denominator)
    assert charge<1
    print('orbit 2 rank at most',len(primes)+2,'last prime',primes[-1],
          'grid denominator',grid,'upper numerator over 10^12',numerator)


if __name__=='__main__':
    main()
