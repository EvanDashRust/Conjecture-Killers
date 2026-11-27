"""Independent exact CRT-grid check of the critical five-adic pair bounds."""
from fractions import Fraction as Q
from itertools import product
from math import gcd, lcm, prod


def coordinates(m):
    result = []
    p = 3
    while m > 1:
        f = 1
        while m % p == 0:
            f *= p
            m //= p
        if f > 1:
            result.append((p,f))
        p += 2
    return result


def bound(rows, adjusted):
    ds = sum((tuple(row) for row in rows), ())
    L = lcm(*ds)
    cr = coordinates(L)
    # Prefix lcm stabilizer acts transitively on lifts of the next class
    # residue having the same value modulo gcd(prefix-lcm, next modulus).
    heights = []
    period = 1
    for d in ds:
        heights.append(gcd(period,d))
        period = lcm(period,d)
    crt_terms = [((L//n)*pow(L//n,-1,n)) for _, n in cr]
    grid = [sum(i*c for i,c in zip(ids,crt_terms)) % L
            for ids in product(*(range(n) for _,n in cr))]
    assert sorted(grid) == list(range(L))
    remainders = [[x%d for d in ds] for x in grid]
    factors = []
    for p,n in reversed(cr):
        gamma=Q(2) if p==3 else (Q(5,4) if p==11 and adjusted else Q(10,7))
        cap = gamma/n
        k, remainder = divmod(cap.denominator, cap.numerator)
        factors.append((n,k,remainder,cap.numerator,cap.denominator))
    best = 0
    for phases in product(*(range(k) for k in heights)):
        vals=[]
        for rem in remainders:
            start=0
            for row in rows:
                if not any(phases[i] == rem[i] for i in range(start,start+len(row))):
                    vals.append(0)
                    break
                start += len(row)
            else:
                vals.append(1)
        for n,k,remainder,num,den in factors:
            groups = (sorted(vals[i:i+n],reverse=True) for i in range(0,len(vals),n))
            vals = [num*sum(g[:k]) + (remainder*g[k] if remainder else 0) for g in groups]
        best = max(best,vals[0])
    return Q(best,prod(item[-1] for item in factors))


def main():
    cases = [
      (((7,11),(21,33)), False, Q(2320,11319)),
      (((7,33),(11,21)), False, Q(220,1029)),
      (((7,39),(13,21)), False, Q(900,4459)),
      (((7,51),(17,21)), False, Q(3260,17493)),
      (((7,57),(19,21)), False, Q(1180,6517)),
      (((7,63),(11,21)), False, Q(5120,33957)),
      (((7,63),(21,27)), False, Q(220,1323)),
      (((7,33),(11,21),(9,)), False, Q(2320,33957)),
      (((7,11),(21,33)), True, Q(635,3234)),
      (((7,13),(21,39)), True, Q(200,1029)),
      (((7,33),(11,21)), True, Q(10,49)),
      (((7,39),(13,21)), True, Q(900,4459)),
      (((7,51),(17,21)), True, Q(3260,17493)),
      (((7,57),(19,21)), True, Q(1180,6517)),
      (((7,63),(11,21)), True, Q(1445,9702)),
      (((7,63),(13,21)), True, Q(5960,40131)),
      (((7,63),(21,27)), True, Q(220,1323)),
    ]
    for rows,changed,expected in cases:
        actual=bound(rows,changed)
        print(rows, changed, actual,flush=True)
        assert actual==expected
    print('All direct CRT-grid values agree.')

if __name__=='__main__':
    main()
