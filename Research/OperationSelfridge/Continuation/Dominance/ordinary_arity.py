"""Restrictions on the number of ordinary integer moduli having at least four prime factors."""
from fractions import Fraction as F
from heapq import nlargest
from arity_tail import BOUND, MAX_ACTIVE, SCALE, primes, up

HEAD5=48
TUNING={3:0,5:0,7:20,11:35,13:40,17:44,19:46,23:46}


def d100(p):
    return TUNING.get(p,50)


def base():
    # Complete ternary expectation is evaluated analytically at each threshold.
    pt=[SCALE]+[up(2*SCALE,3**i) for i in range(1,81)]
    excess=[up(SCALE,3**i) for i in range(81)]
    q5=[up(11*SCALE,15)]+[up(16*SCALE,15*5**y) for y in range(1,HEAD5)]
    # A,B represent the count A*T_3+B, retaining exact cross terms of the 3 and 5 axes.
    pairs=[[(1+y+z,y+(1+y)*z+z*(z-1)//2) for y in range(HEAD5)] for z in range(MAX_ACTIVE)]
    probs=[SCALE]+[0]*(MAX_ACTIVE-1)
    losses=0
    for p in primes(BOUND):
        if p<11:
            continue
        s=p-2; d=d100(p); den=s*(100-d); threshold=s*d
        numer=0
        for mass,row in zip(probs,pairs):
            if not mass:
                continue
            subtotal=0
            for py,(a,b) in zip(q5,row):
                k=max(0,(threshold-100*b)//(100*a)+1)
                i=min(k,80)
                positive=(100*(a*k+b)-threshold)*pt[i]+100*a*excess[i]
                subtotal+=py*positive
            numer+=mass*subtotal
        losses+=up(numer,den*SCALE**2)
        # Conditional distorted level tail P(T>=e) = 100*(p-1)/(den*p**e).
        denom=den*p*p
        zero=denom-100*(p-1)*p
        one=100*(p-1)**2
        new=[]
        geom=0
        for old in probs:
            new.append(up(zero*old+one*geom,denom))
            geom=old+up(geom,p)
        probs=new
    # Bounds with E 2^S <= (p-2)(p-3)/2 and S all previous comparison levels.
    ztail=F(32*BOUND**2,2**(MAX_ACTIVE//2))
    ytail=64*BOUND**2*F(2,5)**HEAD5
    m=64
    far=F(512*4*(8*m+4)*(2*m+2)**2,2**m)
    return F(1,3)+F(losses,SCALE)+ztail+ytail+far


def budget(baseline):
    # First the support is chosen. Each head exponent is an independent label choice.
    keep=1800
    cutoff=2800
    max_power=12
    dp=[[F(1)],[],[],[],[]]
    for p in primes(cutoff):
        if p in (2,7):
            continue
        threshold=F(d100(p),100)
        constant=F(p-1,p-2)/(1-threshold)
        assert constant<=8
        first=constant/p
        new=[row.copy() for row in dp]
        for old_level,row in enumerate(dp):
            # Only the first keep candidates from this sorted product list can survive.
            level=min(4,old_level+1)
            terms=new[level]
            floor=dp[level][keep-1] if len(dp[level])>=keep else 0
            weight=first
            for _ in range(max_power):
                if not row or weight*row[0]<=floor:
                    break
                for a in row:
                    v=a*weight
                    if v<=floor:
                        break
                    terms.append(v)
                weight/=p
        dp=[nlargest(keep,row) for row in new]
    # Every missing large prime has weight < 2/(cutoff-2). Every omitted power
    # has weight <= 8 / 3**(max_power+1), uniformly in the prime and the delta.
    missing=max(F(2,cutoff-2),F(8,3**(max_power+1)))
    top=dp[4]
    def report(label,initial):
        upper=initial
        k=0
        while k<len(top) and upper+top[k]<1:
            upper+=top[k]
            k+=1
        assert k<len(top) and top[k]>dp[3][0]*missing
        print(label,"baseline upper /10^12",up(initial.numerator*10**12,initial.denominator),
              "max extras",k,"upper /10^12",up(upper.numerator*10**12,upper.denominator),
              "necessary count",k+1,flush=True)
    report("7 absent",baseline)
    # The only larger concentration constant is at 11; omitting 7 more than pays for it.
    def second(p,threshold):
        c=F(p-1,p-2)/(1-threshold)
        return 1+c*F(3*p-1,(p-1)**2)
    ratio=second(11,F(35,100))/(second(11,F(1,3))*second(7,F(1,5)))
    assert ratio<1
    far=F(36711,10**6)*ratio
    print("Schroeder unrestricted tail ratio",ratio,"tail upper",far)
    report("7 absent and only counting P+<=10^9 exceptions",baseline+far)


if __name__=='__main__':
    budget(base())
