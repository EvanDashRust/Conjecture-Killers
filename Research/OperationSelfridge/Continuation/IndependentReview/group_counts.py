"""Group-tail and grid certificates for simultaneous 7/11/13 counting."""
from fractions import Fraction as F
from functools import cache
from itertools import product
from math import comb, gcd, lcm, prod
from common_hole import EARLY, MISSING_FIFTEEN, factors

GROUP = (9,5,3,15,13,17,27,39,19,23,45,25,51,57,31,29)
GROUP13 = (15,9,5,3,11,17,33,27,19,23,45,25,51,57,29,31)
LIMIT = 10000


def group_weights(group, h, W):
    # For independent comparison exponents, E[prod(I_i, i in S)]=W(lcm(S)).
    size = 1 << len(group)
    D = [1]*size
    for i in range(1,size):
        bit = i & -i
        D[i] = lcm(D[i-bit], group[bit.bit_length()-1])
    weights = {d:W(d) for d in set(D)}
    scale = lcm(*(v.denominator for v in weights.values()))
    moments = [int(weights[d]*scale) for d in D]
    hs = scale*h.numerator
    count = [i.bit_count() for i in range(size)]
    best = [hs*(len(group)+1)]*size
    for t in range(len(group)+1):
        coef = [0]*(len(group)+1)
        if t:
            for j in range(t+1,len(group)+1):
                coef[j] = (-1)**(j-t-1)*comb(j-2,t-1)
        else:
            coef[1]=1
        # Newton coefficients for the integer hinge; verify the identity on all inputs.
        assert all(sum(comb(s,j)*coef[j] for j in range(s+1)) == max(0,s-t)
                   for s in range(len(group)+1))
        values = [x*coef[k] for x,k in zip(moments,count)]
        for i in range(len(group)):
            step=1<<i
            for start in range(step,size,2*step):
                for j in range(start,start+step):
                    values[j] += values[j-step]
        assert min(values) >= 0
        best = [min(v, t*hs+x*h.denominator) for v,x in zip(best, values)]
    maxima=[0]*(len(group)+1)
    for k,v in zip(count,best):
        maxima[k]=max(maxima[k], v)
    return [F(x,hs) for x in maxima]


def weight_function(schedule):
    @cache
    def W(d):
        v=F(1,d)
        for q,_ in factors(d):
            if q==3: v*=2
            elif q==5: v*=F(4,3)
            else: v*=1/(1-F(schedule[q],q-1)) if q in schedule else F(10,7)
        return v
    return W


def groups(case):
    ps, excluded, group, h, schedule = case
    W=weight_function(schedule)
    maxima=group_weights(group,h,W)
    for p,k in ps:
        other=[]
        for b in range(1,LIMIT,2):
            if b%excluded==0 or b in group:continue
            d=b
            while d%p==0:d//=p
            other.append(min(F(1),W(d)/h)*F(d,b))
        other.sort(reverse=True)
        assert len(set(group))==len(group) and all(d%p and d%excluded for d in group)
        assert (other[k-1]*h)**4*LIMIT**3 > F(16,3)
        prefix=[F(0)]
        for v in other[:k]:prefix.append(prefix[-1]+v)
        total=max(v+prefix[k-s] for s,v in enumerate(maxima) if s<=k)
        assert total<p
        print(f"p={p}, k={k}, group upper {total} < {p} ({float(total):.10f})",flush=True)


def profiles(n,a):
    return [(z,s) for z in range(n+1) for s in range(n-z+1)
            if s+2*(n-z-s)<=a and (n>z+s or a==s)]


def grid():
    survivors=set()
    for a,b,c in product(range(20),repeat=3):
        if a+b+c>19 or a+c<7 or b+c<11:continue
        for (z,s),(u,t) in product(profiles(7,a),profiles(11,b)):
            required=2*z*u-min(3,z*u)+max(0,s-3)*u+z*max(0,t-3)
            if c>=required:survivors.add((a,b,c,z,s,u,t))
    expected={(7,11,0,0,7,0,11),(7,11,1,0,7,0,11),(7,12,0,0,7,0,10),(8,11,0,0,6,0,11)}
    assert survivors==expected
    print("Grid survivors before full 11-fibre test:",sorted(survivors))
    W=weight_function(EARLY)
    h=F(181617,10**6)
    # Apply W(d)^4 <= (16/3) d^-3 in each of the three checks.
    assert LIMIT**3*(h-F(1,9))**4 > F(16,3)
    ds=[d for d in range(1,LIMIT,2) if d%7 and d%11]
    tau=lambda d:prod(e+1 for _,e in factors(d))
    assert max(tau(d) for d in ds if W(d)>=h)==3
    assert {d for d in ds if W(d)>F(1,9)}=={1,3,5,9,15}
    cap=max(tau(d) for d in ds if W(d)>=h-F(1,9))
    assert cap<9
    print("After thinning one seven-root, common singleton cofactors at most",cap,"< 9")


if __name__=="__main__":
    # For this common group the exact maxima are identical. The complement and
    # the coordinate receiving the restoration differ between 7 and 11.
    for p, excluded, k in ((7,11,19),(11,7,57)):
        groups(([(p,k)],excluded,GROUP,F(181617,10**6),EARLY))
    groups(([(13,44)],7,GROUP13,F(119046,10**6),MISSING_FIFTEEN))
    grid()
