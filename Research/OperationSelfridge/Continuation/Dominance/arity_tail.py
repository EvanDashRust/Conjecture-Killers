"""Exact unlimited-rank arity obstruction for the (2,1,1,0,...) prefix heights."""
from fractions import Fraction as F
from itertools import combinations
from math import isqrt, lcm, prod
from heapq import nlargest

SCALE=10**20
BOUND=128**2
MAX_ACTIVE=160
DELTAS={3:0,5:0,7:20,11:30,13:35,17:40,19:40,23:46}


def delta(p):
    return DELTAS.get(p,49 if p<101 else 50)


def primes(stop):
    prime=bytearray([1])*stop
    prime[:2]=b'\x00\x00'
    for p in range(2,isqrt(stop-1)+1):
        if prime[p]:
            prime[p*p::p]=b'\x00'*len(range(p*p,stop,p))
    return [p for p in range(2,stop) if prime[p]]


def up(n,d):
    return -(-n//d)


def integers_at(values):
    common=lcm(*(q.denominator for q in values))
    return [q.numerator*(common//q.denominator) for q in values],common


def head(branch):
    caps=[[F(6 if branch=='sibling' else 5,9),F(2,9),F(1,9)],
          [F(4,15),F(1,15)],[F(6,35),F(1,35)]]
    total=F(0)
    states=[((),F(1))]
    for p,cap in zip((3,5,7),caps):
        d=F(delta(p),100)
        tails=[F(1)]+[v/(1-d) for v in cap]+[F(0)]
        assert all(a>=b for a,b in zip(tails,tails[1:]))
        new=[]
        for marks,weight in states:
            count=sum(marks)+sum(a*b for a,b in combinations(marks,2))
            total+=weight*max(0,count*sum(cap)-d)/(1-d)
            for k,(u,v) in enumerate(zip(tails,tails[1:])):
                new.append((marks+(k,),weight*(u-v)))
        states=new
    return total,states,caps


def infinite_charge(branch):
    total,states,caps=head(branch)
    weights,H=integers_at([w for _,w in states])
    # Combine equal head signatures prior to the finite integer recursion.
    signatures={}
    for (marks,_),weight in zip(states,weights):
        k,l=sum(marks),sum(a*b for a,b in combinations(marks,2))
        signatures[k,l]=signatures.get((k,l),0)+weight
    assert sum(signatures.values())==H
    range_z=range(MAX_ACTIVE)
    vectors=[[k+l+(1+k)*z+z*(z-1)//2 for k,l in signatures] for z in range_z]
    weight=list(signatures.values())
    probabilities=[SCALE]+[0]*(MAX_ACTIVE-1)
    losses=0
    for p in primes(BOUND):
        if p<11:
            continue
        s=p-2
        d=delta(p)
        den=s*(100-d)
        # term G = E [(100 * load_count - s*d)_+] / den, over the head.
        numerator=0
        threshold=s*d
        for mass,values in zip(probabilities,vectors):
            if mass and 100*values[-1]>threshold:
                # The final signature corresponds to the maximal level in all three heads.
                numerator+=mass*sum(w*max(0,100*v-threshold) for v,w in zip(values,weight))
        losses+=up(numerator,H*den)
        probabilities=[up((den-100)*a+100*b,den) for a,b in zip(probabilities,[0]+probabilities[:-1])]
    assert all(values[-1]==max(values) for values in vectors)
    # Sum the contribution from S >= MAX_ACTIVE for p < BOUND.
    trunc=F(64*BOUND**2,90*2**(MAX_ACTIVE//2))
    # Group all n >= 128**2 into consecutive square blocks and pair adjacent blocks.
    # Each pair from k=2m,2m+1 has at most 8m+4 integers, each <(2m+2)**2,
    # and 2**(-sqrt(n)/2) <= 2**(-m).  Successive majorants have ratio <=3/4.
    m=64
    far=F(1024,90)*4*(8*m+4)*(2*m+2)**2/F(2**m)
    assert F(8*(m+1)+4,8*m+4)*F(2*m+4,2*m+2)**2 / 2 < F(3,4)
    charge=total+F(losses,SCALE)+trunc+far
    return charge,caps,trunc,far


def arity_budget(branch):
    baseline,caps,trunc,far=infinite_charge(branch)
    # Top products for distinct supports and modes. Distinct labels can have equal weights.
    largest=[[],[],[],[],[]]
    largest[0]=[F(1)]
    limit=600
    cutoff=1000
    for p in primes(cutoff):
        if p==2:
            continue
        alpha=caps[(3,5,7).index(p)] if p<11 else [F(1,p-2)]
        w=[a/(1-F(delta(p),100)) for a in alpha]
        new=[a.copy() for a in largest]
        for i in range(5):
            new[min(i+1,4)].extend(a*b for a in largest[i] for b in w)
        largest=[nlargest(limit,row) for row in new]
    tail_cap=largest[3][0]*F(2,cutoff-2)
    top=largest[4]
    assert top[-1]>tail_cap
    upper=baseline
    k=0
    while upper+top[k]<1:
        upper+=top[k]
        k+=1
    print(branch,'base upper /10^12',up(baseline.numerator*10**12,baseline.denominator),
          'finite truncation <10^-15',trunc<F(1,10**15),'infinite tail <10^-9',far<F(1,10**9))
    print('permitted arbitrary high-arity labels',k,'upper /10^12',up(upper.numerator*10**12,upper.denominator),
          'required in a cover',k+1)
    return k


if __name__=='__main__':
    for branch in ('third','sibling'):
        arity_budget(branch)
