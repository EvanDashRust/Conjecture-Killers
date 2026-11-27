"""Remove only large-prime classes with high small-prime exponents, retaining the full smooth head."""
import argparse
from fractions import Fraction as Q
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'Review'))
from joint_fibres import UNIT, LIMIT, CAP, ceiling, capped_exponent, check_loss, primes_through
from third_prime import MISSING_FIFTEEN

SCHEDULE = {**MISSING_FIFTEEN,11:3,13:4,19:6}
CASES = {"high3": (2,None), "high5": (None,1), "both": (2,1), "next": (3,2)}

def capped_factor(p, g, t, height):
    law = capped_exponent(p,g)
    shift = t-g/p
    law[0] -= shift
    law[1] += shift
    if height is None:
        first = 1+g/(p-1)+shift
        third = 1+g*(7*p*p-2*p+1)/(p-1)**3+7*shift
    else:
        assert 1<=height<CAP
        law = law[:height]+[sum(law[height:])]
        tails = [t]+[g/p**j for j in range(2,height+1)]
        first = 1+sum(tails)
        third = 1+sum(tail*((j+1)**3-j**3) for j,tail in enumerate(tails,1))
    assert sum(law)==1 and min(law)>=0
    return law,first,third

def head_law(t,h3,h5):
    def head(g3,g5):
        a,m,c=capped_factor(3,g3,t,h3)
        b,n,d=capped_factor(5,g5,g5/5,h5)
        hist={}
        for i,x in enumerate(a,1):
            for j,y in enumerate(b,1):
                hist[i*j]=hist.get(i*j,0)+ceiling(UNIT*x*y)
        return hist,ceiling(UNIT*m*n),ceiling(UNIT*c*d)
    return head

def residual(orbit,h3,h5,t,schedule):
    g3,g5=Q(2),Q(4,3)
    # Full smooth head, including high powers removed from the *tail alphabet*.
    mixed = (1-t if orbit==1 else t)*g5/5 + t*g5/20 + (g3/6)*(g5/4)
    parts=check_loss(primes_through(LIMIT),g3,g5,head_law(t,h3,h5),11,schedule)
    return 1 - mixed - sum(parts)

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('case',choices=CASES)
    parser.add_argument('--endpoint',type=int,choices=(0,1),required=True)
    args=parser.parse_args()
    t=[Q(5,9),Q(2,3)][args.endpoint]
    h3,h5=CASES[args.case]
    # The orbit influences only the head cost. Compute the slow recursion once.
    # The old schedule already suffices for high3. Tune for high5.
    schedule=SCHEDULE if args.case=='high5' else MISSING_FIFTEEN
    second=residual(2,h3,h5,t,schedule)
    first=second+(2*t-1)*Q(4,15)
    print(f"{args.case} t={t} r1={first} ({float(first):.12f}) r2={second} ({float(second):.12f})",flush=True)
    assert first>0 and (args.case=='next' or second>0)
