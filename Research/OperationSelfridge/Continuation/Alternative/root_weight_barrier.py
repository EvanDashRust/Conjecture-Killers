"""Finite lower certificate for the scalar two-root reweighting relaxation."""
from fractions import Fraction as Q
from itertools import accumulate
from joint_savings import SCALE, SCHEDULE, down, parameters, primes_through

HEIGHT = 6
HORIZON = 8009
CAP = 1024


def lower_prices():
    # Prices of (dR-t)_+ minus ((d-1)R-t)_+, with d=1,...,HEIGHT+1.
    # R starts at the five-coordinate and acquires the preceding rough factors.
    v = (1-Q(1,5**HEIGHT))/4
    g5 = 1/(1-v)
    R = [0]*(CAP+1)
    survivals=[Q(1)]+[g5/5**i for i in range(1,HEIGHT+1)]+[Q(0)]
    for i in range(1,HEIGHT+2):
        R[i]=down(SCALE*(survivals[i-1]-survivals[i]))
    prices=[0]*(HEIGHT+2)
    for p in primes_through(HORIZON):
        if p<11:
            continue
        t,g = parameters(p,SCHEDULE)
        a,b = t.as_integer_ratio()
        gn,gd=g.as_integer_ratio()
        m=list(accumulate(R))
        w=list(accumulate(i*x for i,x in enumerate(R)))
        for d in range(1,HEIGHT+2):
            k=min(CAP,a//(b*d))
            l=CAP if d==1 else min(CAP,a//(b*(d-1)))
            numer=b*d*(w[l]-w[k])-a*(m[l]-m[k])+b*(w[CAP]-w[l])
            prices[d]+=numer*gn//(b*gd*(p-1))
        # Clip every rough factor at four and R at CAP for a lower price.
        tail=[Q(1),g/p,g/p**2,g/p**3,Q(0)]
        pm=[down(SCALE*(tail[i]-tail[i+1])) for i in range(4)]
        nxt=[0]*(CAP+1)
        for i,x in enumerate(R):
            if x:
                for j,prob in enumerate(pm,start=1):
                    nxt[min(i*j,CAP)]+=prob*x//SCALE
        R=nxt
    return [Q(x,SCALE) for x in prices]


def main():
    prices=lower_prices()
    U=(1-Q(1,3**HEIGHT))/2
    V=(1-Q(1,5**HEIGHT))/4
    g5=1/(1-V)
    s1,s2=Q(2,3)-U,Q(1,3)
    # Every pure ternary class other than 0 mod 3 is in root 1.
    high=sum(prices[e+1]/3**e for e in range(2,HEIGHT+1))
    inc1=prices[2]+high/s1
    inc2=prices[2]+high/s2
    def lower(lam):
        charge = g5*(max(lam/s1,(1-lam)/s2)*(U-Q(1,3))*V
                     + lam/5+max(lam,1-lam)*(V-Q(1,5)))
        return charge+prices[1]+max(lam*inc1,(1-lam)*inc2)
    breaks = [Q(0), Q(1), Q(1,2), s1/(s1+s2), inc2/(inc1+inc2)]
    value,lam=min((lower(x),x) for x in breaks)
    print("height",HEIGHT,"last rough stage",HORIZON,"lower charge",value,
          "decimal",float(value),"minimum at weight",lam)
    assert value>1


if __name__=='__main__':
    main()
