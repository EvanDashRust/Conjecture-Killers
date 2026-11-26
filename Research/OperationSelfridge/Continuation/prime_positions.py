"""Unrestricted bounds on initial primes in the period of an odd distinct covering."""
from fractions import Fraction as Q
from math import prod
from frozen_prefix_tail import primes_to,distortion,up,SCALE


def backwards(primes,cut,split):
    # Price the entire large-prime tail once per unit of incoming second moment.
    finite,tail=distortion(primes,cut,split,Q(1),Q(1,3),[])
    value=up((finite+tail).numerator*SCALE,(finite+tail).denominator)
    values={}
    for p in reversed(primes):
        if p>=cut:continue
        r=p-1
        # Every delta=i/40 yields a valid loss and new moment cap. Choose the smallest.
        increment=min(up(40**2*SCALE+i*160*(3*p-1)*value,
                         4*i*(40-i)*r*r) for i in range(1,40))
        value+=increment
        values[p]=Q(value,SCALE)
    return values


def old(primes):
    weight=[Q(1,p-2) for p in primes]
    lost=prod(1+w for w in weight)-1-sum(weight)
    if len(primes)==4:
        # At least one intersection per disjoint pair of supports in the dependency
        # polynomial bound. Three pair partitions. See PRIME_POSITIONS.md.
        lost-=3*prod(weight)
    second=prod(1+Q(3*p-1,(p-1)*(p-2)) for p in primes)
    return lost,second


if __name__=="__main__":
    split=21
    primes=primes_to(2**split)
    future=backwards(primes,1009,split)
    for s in [2,3,4]:
        head,second=old([3,5,7,11][:s])
        cut=next(p for p in primes if p>11 and p in future and head+second*future[p]<1)
        x=head+second*future[cut]
        print("number below",cut,">=",s+1,"head loss <=",head,
              "outward total upper / 10^12",up(x.numerator*10**12,x.denominator))
