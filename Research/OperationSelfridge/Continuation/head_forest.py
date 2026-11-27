"""Disjoint-support forest under a partial projection of small-prime powers."""
from fractions import Fraction as Q
from itertools import combinations
from math import prod
from prime_positions import backwards,primes_to,up


def forest_union(weights):
    parent={k:k for k in weights}
    neighbors={k:[] for k in weights}
    def root(k):
        while parent[k]!=k:
            k=parent[k]
        return k
    edges=sorted(((weights[v]*weights[w],v,w) for v,w in combinations(weights,2)
                  if not v&w),reverse=True)
    for _,v,w in edges:
        if root(v)!=root(w):
            parent[root(v)]=root(w)
            neighbors[v].append(w)
            neighbors[w].append(v)
    def maximum(v,prev):
        zero=Q(0); one=weights[v]
        for child in neighbors[v]:
            if child!=prev:
                no,yes=maximum(child,v)
                zero+=max(no,yes)
                one+=max(no,yes-weights[v]*weights[child])
        return zero,one
    return sum(max(maximum(v,None)) for v in parent if root(v)==v)


def projected(primes,removed):
    # For each directed (a,b), project the labels p_a*p_b^e onto p_b^e.
    # No reverse pair may be projected, so each such numerical label has one owner.
    assert len(primes)==len(set(primes))
    assert all(a!=b and (b,a) not in removed for a,b in removed)
    n=len(primes)
    unary=[1+sum(b==i for a,b in removed) for i in range(n)]
    assert all(u<p-1 for p,u in zip(primes,unary))
    gamma=[Q(p-1,p-1-u) for p,u in zip(primes,unary)]
    w=[g/(p-1) for g,p in zip(gamma,primes)]
    caps={}
    for mask in range(1,1<<n):
        if mask.bit_count()<2:continue
        cap=prod(v for i,v in enumerate(w) if mask>>i&1)
        for a,b in removed:
            if mask==(1<<a|1<<b):cap/=primes[a]
        caps[mask]=min(Q(1),cap)
    return forest_union(caps),prod(1+g*Q(3*p-1,(p-1)**2) for g,p in zip(gamma,primes))


if __name__=="__main__":
    primes=primes_to(2**21)
    future=backwards(primes,1009,21)
    policies=[([3,5,7,11],{(0,2),(0,3)}),
              ([3,5,7,11,13],{(0,2),(0,3),(0,4),(1,4)})]
    for head,edges in policies:
        loss,u=projected(head,edges)
        cut=min(p for p,v in future.items() if loss+u*v<1 and p>max(head))
        x=loss+u*future[cut]
        print(head,"head survivor >=",1-loss,"second moment <=",u)
        print("at least",len(head)+1,"prime divisors below",cut,"upper / 1e12",
              up(x.numerator*10**12,x.denominator))
