"""Dichotomy for the third prime and weighted incidence counts."""
from argparse import ArgumentParser
from fractions import Fraction as Q
from joint_fibres import UNIT, EARLY, primes_through, LIMIT, capped_exponent, moments, ceiling, check_loss


def product_head(g3, g5):
    hist = {}
    for i,x in enumerate(capped_exponent(3,g3)):
        for j,y in enumerate(capped_exponent(5,g5)):
            n=(1+i)*(1+j)
            hist[n]=hist.get(n,0)+ceiling(UNIT*x*y)
    def cube(p,g):
        a,b,c=moments(p,g)
        return 1+3*a+3*b+c
    m=(1+g3/2)*(1+g5/4)
    return hist,ceiling(UNIT*m),ceiling(UNIT*cube(3,g3)*cube(5,g5))


def joint_counts(h, excluded):
    # All primes other than 7 and 11 carry the conditional caps.
    limit=100_000
    factors=[Q(1)]*(limit+1)
    for p in primes_through(limit):
        if p in (2,7,11):
            continue
        if p==3:g=Q(2)
        elif p==5:g=Q(4,3)
        else:g=1/(1-(Q(EARLY[p],p-1) if p in EARLY else Q(3,10)))
        assert g**4 <=p*(Q(16,3) if p==3 else 1)
        for m in range(p,limit+1,2*p):
            factors[m]*=g
    ranked=[]
    for m in range(3,limit+1,2):
        if (m%7 and m%11) or any(m%p==0 for p in excluded):
            continue
        d=m
        while d%7==0:d//=7
        while d%11==0:d//=11
        weight=min(h,factors[d]/d)*Q(d,m)
        ranked.append((weight,m))
    ranked.sort(reverse=True)
    tot=Q(0)
    for i,(w,m) in enumerate(ranked,1):
        if tot+w>=h:
            break
        tot+=w
    # W(m)^4 is at most (16/3)/m^3 by factoring.
    if i>1:
        assert ranked[i-2][0]**4*limit**3 > Q(16,3)
    return i,tot


MISSING_FIFTEEN = {11:2,13:3,17:4,19:5,23:6,29:8,31:8,37:12,41:12,
                   43:12,47:16,53:16,59:16,61:16,67:20,71:24,73:24}


def count_15_without_7(h):
    cutoff=200_000
    f=[Q(1)]*(cutoff+1)
    for p in primes_through(cutoff):
        if p in (2,7):
            continue
        gamma = (Q(2) if p==3 else Q(4,3) if p==5 else
                 1/(1-(Q(EARLY[p],p-1) if p in EARLY else Q(3,10))))
        assert gamma**4 <= p*(Q(16,3) if p==3 else 1)
        for m in range(p,cutoff+1,2*p):
            f[m]*=gamma
    all_multiples=[]
    three_prime=[]
    for m in range(15,cutoff+1,30):
        if m%7==0:
            continue
        d=m
        while d%3==0:
            d//=3
        while d%5==0:
            d//=5
        all_multiples.append((f[m]/m,m))
        if d>1:
            three_prime.append(all_multiples[-1])
    for ranked,target,count in [(all_multiples,h,50),(three_prime,h-Q(1,3),36)]:
        take=sorted(ranked,reverse=True)[:count-1]
        assert take[-1][0]**4 * cutoff**3 > Q(16,3)
        upper=sum(x for x,_ in take)
        assert upper<target
        print("Required mixed count",count,"previous sum upper",upper,flush=True)


HEAD_SCHEDULE = {11:2,13:3,17:4,19:4,23:6,29:8,31:8,37:8,41:10,43:12}


def main():
    parser=ArgumentParser()
    parser.add_argument("--missing-with-seven", type=int, choices=(3,5,9,15))
    parser.add_argument("--mixed-count",action="store_true")
    parser.add_argument("--second-missing-prime",type=int,choices=(13,17,19))
    args=parser.parse_args()
    if args.mixed_count:
        prefix,middle,tail=check_loss(primes_through(LIMIT),Q(2),Q(4,3),minimum_prime=11)
        bound=1-prefix-middle-tail
        print("Uncovered after deleting all multiples of 15",bound,float(bound))
        target=Q(535333,1_000_000)
        assert bound>target
        count_15_without_7(target)
        return
    if args.second_missing_prime:
        g3,g5=Q(2),Q(4,3)
        a,b,c=check_loss(primes_through(LIMIT),g3,g5,product_head,11,MISSING_FIFTEEN,
                         omit_stages=(args.second_missing_prime,))
        h=1-g3*g5/8-a-b-c
        targets={13:Q(119046,10**6),17:Q(32890,10**6),19:Q(6492,10**6)}
        assert h>targets[args.second_missing_prime]
        print("Additional omitted prime",args.second_missing_prime,"uncovered",h,float(h))
        return
    if args.missing_with_seven==15:
        g3,g5=Q(2),Q(4,3)
        lower=11
        schedule=MISSING_FIFTEEN
    elif args.missing_with_seven:
        g3,g5={3:(Q(6,5),Q(4,3)),5:(Q(2),Q(20,19)),9:(Q(18,11),Q(4,3))}[args.missing_with_seven]
        lower=11
        schedule=HEAD_SCHEDULE
    else:
        g3,g5=Q(2),Q(4,3)
        lower=13
        schedule=EARLY
    prefix,middle,tail=check_loss(primes_through(LIMIT),g3,g5,product_head,lower,schedule)
    h=1-g3*g5/8-prefix-middle-tail
    if args.missing_with_seven==15:
        h+=g3*g5/15
    print("prefix",prefix,"middle",middle,"tail",tail,flush=True)
    print("uncovered",h,float(h),flush=True)
    if args.missing_with_seven:
        assert h>0
        return
    target=Q(181617,1_000_000)
    assert h>target
    for exc,expected in [((),9),((7,),29),((11,),10)]:
        n,old=joint_counts(target,exc)
        assert n==expected
        print("excluded primes",exc,"required count",n,"previous weight",old,flush=True)

if __name__=='__main__':
    main()
