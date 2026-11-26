"""Independent finite-rank arithmetic using exact tail summation of the Bellman kernel."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
import json
from math import isqrt
from pathlib import Path

UNIT = 10**24


def ceil(num, den):
    return (num+den-1)//den


def backward(primes, schedule):
    edge = max(schedule)+1
    v = [0]*(edge+1)
    a = b = 0
    for p,t in reversed(list(zip(primes,schedule))):
        r=p-1
        out=[0]
        assert 0<=2*t<=r
        for m in range(1,edge+1):
            # Conditional on J=1+T >= stop, E[J] = stop+1/r.
            stop=max(2, edge//m+1)
            tail=ceil(a*m*(r*stop+1)-b*r,r)
            for j in reversed(range(2,stop)):
                tail=ceil(r*v[m*j]+tail,p)
            # Tail is now an upper bound given a *positive* exponent.
            # Evaluate the two actual positive-probability kernels separately.
            def K(denom):
                return F((p*denom-r)*v[m]+r*tail,p*denom)
            cden=r-t
            kden=r-min(m,t)
            charge=UNIT*F(max(m-t,0),cden)
            val=charge+max(K(kden),K(cden)-UNIT*F(kden-cden,kden))
            out.append(ceil(val.numerator,val.denominator))
        a=ceil(a*(r-t+1)+UNIT,r-t)
        b+=UNIT*t//(r-t)
        v=out
    return edge,v,a,b


def estimate(table,x):
    edge,v,a,b=table
    def at(m):
        return v[m] if m<=edge else a*m-b
    lo=int(x)
    return F(at(lo)+(x-lo)*(at(lo+1)-at(lo)),UNIT)


def geom(p,g,z,k):
    def tail(j):
        return F(1) if j==0 else z if j==1 else g/p**j
    return tail(k)-tail(k+1)


def orbit1(table,z):
    edge,v,a,b=table
    g3,g5=F(2),F(4,3)
    mu=(1+z+g3/6)*(1+g5/4)
    expense=g5*((1-z)/5+z/20+F(1,12))
    # Integrate over the untruncated law. All products above the edge
    # already use the affine upper branch, so the finite correction is exact.
    cost=a*mu-b
    for i in range(1,edge+1):
        w=geom(3,g3,z,i-1)
        for j in range(1,edge//i+1):
            cost+=w*geom(5,g5,g5/5,j-1)*(v[i*j]-a*i*j+b)
    return expense+cost/UNIT


def quantile_law():
    H=[i for i in range(45) if i%3 and i%5 and i%15!=1 and i%9!=2]
    n=len(H)
    assert n==17
    mods=(1,3,9,5,15,45)
    classes=[[sum(1<<i for i,c in enumerate(H) if c%d==t) for t in range(d)] for d in mods]
    profiles=[set() for _ in range(n+1)]
    for mask in range(1<<n):
        profiles[mask.bit_count()].add(tuple(max((mask&u).bit_count() for u in family)
                                              for family in classes))
    profile=next(iter(profiles[n]))
    mean=sum(x*y for x,y in zip(profile,[1,1,F(3,2),F(5,4),F(5,4),F(15,8)]))/n
    law=defaultdict(F)
    def prob(p,i):
        if i==10:
            return F(1,p**9)
        return F(p-1,p**i)
    for i,j in product(range(1,11),repeat=2):
        weights=(1,1,i,j,j,i*j)
        support=[max(sum(x*y for x,y in zip(vec,weights)) for vec in layer) for layer in profiles]
        deficits=[support[n]-u for u in reversed(support)]
        k=0
        while k<n:
            # The next line of larger slope crosses the current line first
            # at this minimum; skip all intermediate lines tied at the break.
            threshold,k2=min((F(deficits[t]-deficits[k],t-k),-t)
                             for t in range(k+1,n+1))
            k2=-k2
            law[threshold]+=prob(3,i)*prob(5,j)*F(k2-k,n)
            k=k2
    assert sum(law.values())==1
    s=F(45,68)
    to_remove=1-s
    retained={}
    for x,w in sorted(law.items()):
        removed=min(to_remove,w)
        to_remove-=removed
        if w>removed:retained[x]=w-removed
    slack=mean-sum(x*w for x,w in law.items())
    assert min(retained)==F(4,3) and sum(retained.values())==s
    assert sum(x*w for x,w in retained.items())+slack==F(893,408)
    return retained,slack


def main():
    schedules=json.loads((Path(__file__).resolve().parents[1]/'PrimeSupport/schedules.json').read_text())
    primes=[n for n in range(11,5001) if all(n%d for d in range(2,isqrt(n)+1))]
    for key,schedule in schedules.items():
        table=backward(primes[:len(schedule)],schedule)
        if key=='1':
            charges=[orbit1(table,z) for z in (F(5,9),F(2,3))]
        else:
            law,slack=quantile_law()
            charges=[1-sum(law.values())+sum(w*estimate(table,x) for x,w in law.items())
                     +slack*F(table[2],UNIT)]
            print('orbit 2 retained atoms',len(law),'linear slack',slack,flush=True)
        for charge in charges:
            print('orbit',key,'rank at most',len(schedule)+2,'upper numerator over 10^12',
                  ceil(charge.numerator*10**12,charge.denominator),flush=True)
            assert charge<1


if __name__=='__main__':
    main()
