"""Higher-moment certificates for independent fresh-prime blocks."""
from fractions import Fraction as Q
from harrington_obstruction import *
from math import comb, factorial
from bisect import bisect_right

def moment(a,m):
    # ordinary powers of x expanded in falling factorials via Stirling numbers.
    S=[[1]]
    for j in range(1,m):S.append([0]+[(S[-1][k-1] if k-1<len(S[-1]) else 0)+(k*S[-1][k] if k<len(S[-1]) else 0) for k in range(1,j+1)])
    def one(p,b):
        r=Q(1,p);t=r/(1-r)
        geom=[sum(c*factorial(j)*t**j for j,c in enumerate(row))/(1-r) for row in S]
        return 1+sum(comb(m,j)*(2**(m-j)-1)*geom[j] for j in range(m))/b
    return prod(one(p,b) for p,b in zip(PRIMES,a))

def compute():
    from fractions import Fraction as F
    W=old_groups();a=condition_single_coordinates(W)
    alive=shearer_survival([F(ceil_ratio(w.numerator*GROUP_SCALE,w.denominator),GROUP_SCALE) for w in W])
    sieve=prime_sieve(PRIME_LAST);prime=[p for p in range(19,PRIME_LAST+1) if sieve[p]]
    M2=moment(a,2)
    c=fresh_sums(a);assert M2==c[2]
    MASS=divisor_count_upper(a,CONVEX_LAST)
    D=prod(1+F(p,p-1)/s for p,s in zip(PRIMES,a));DS=scaled_ceil(D)
    pre,weighted=[0],[0]
    for i,u in enumerate(MASS[1:],1):pre.append(pre[-1]+u);weighted.append(weighted[-1]+i*u)
    base=[F(0)]
    for p in prime:
        v=F(min(ceil_ratio(DS-t*SCALE+t*pre[t]-weighted[t],p-1-t) for t in range(p-1)),SCALE) if p<=CONVEX_LAST else M2*F(ceil_ratio(SCALE,(p-1)**2),SCALE)
        base.append(base[-1]+v)
    certified=False
    for m in (2,3,4,5,6,7,8):
        mm=moment(a,m); su=[0]*(len(prime)+1)
        for j in range(len(prime)-1,-1,-1):
            u=prime[j]-1
            su[j]=su[j+1]+ceil_ratio(SCALE*(2*u+1)**m,2*u**(2*m))
        T=(2+F(1,PRIME_LAST))**m*F(1,2*(m-1)*(PRIME_LAST-1)**(m-1))
        for cut in range(19,2501):
            j=bisect_right(prime,cut)
            if prime[j-1]!=cut: continue
            z=base[j]+mm*(F(su[j],SCALE)+T)
            if z<alive:
                print(m,cut,float(z),float(alive-z),flush=True)
                if m==4:
                    assert cut==239
                    assert scaled_ceil(z)==322270769143343303
                    assert (alive.numerator*SCALE)//alive.denominator==322332585347204393
                    certified=True
                    print('outward ceil e18:',scaled_ceil(z),'survival floor:',(alive.numerator*SCALE)//alive.denominator)
                break
    assert certified
if __name__=='__main__':compute()
