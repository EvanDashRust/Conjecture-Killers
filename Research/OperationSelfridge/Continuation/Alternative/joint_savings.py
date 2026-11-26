"""Rigorous Eq. (36) improvements to the scalar first-orbit prime exclusions."""
from argparse import ArgumentParser
from fractions import Fraction as Q
from itertools import accumulate
from power_orbits import product_initial, primes_through, check_loss, LIMIT
from third_prime import MISSING_FIFTEEN

SCALE = 10**16
SCHEDULE = {**MISSING_FIFTEEN, 11:3, 13:4, 19:6, 79:24, 83:24, 89:30,
            97:32, 101:32, 103:32, 107:32, 109:32, 113:36, 127:40,
            131:48, 137:48, 139:48, 149:48}
# (last joint stage, last later stage used to bound local savings)
WINDOWS = {37:(47,349), 41:(131,1201), 43:(211,3001), 47:(499,8009)}
CAP_R = 128
MAX_EXP = 3


def down(x):
    return x.numerator // x.denominator


def parameters(p):
    r = p-1
    t = Q(SCHEDULE[p]) if p in SCHEDULE else Q(3*r, 10)
    return t, r/(r-t)


def steps(primes):
    out = {}
    for q in primes:
        t, g = parameters(q)
        # floor masses at R multipliers 1,2,3,4. Last bin includes all T>=3.
        def tail(k):
            return g/q**k
        pm = [1-tail(1),tail(1)-tail(2),tail(2)-tail(3),tail(3)]
        out[q] = (t,g,[down(SCALE*x) for x in pm])
    return out


def local_B(p, future, schedule):
    # The region with a positive distortion improvement has d<t_p.
    t, _ = parameters(p)
    D = -(-t.numerator//t.denominator)
    result = [0]*D
    R = [0]*(CAP_R+1)
    R[1] = SCALE
    for q in future:
        tq, gamma, pm = schedule[q]
        a,b = tq.as_integer_ratio()
        gn,gd = gamma.as_integer_ratio()
        pref = list(accumulate(R))
        weighted = list(accumulate(j*x for j,x in enumerate(R)))
        for d in range(1,D):
            for e in range(1,MAX_EXP+1):
                lo,hi = e*d,(e+1)*d
                # Three pieces of (hi R-t)_+ - (lo R-t)_+, all nonnegative.
                k = min(CAP_R, a//(b*hi))
                l = min(CAP_R, a//(b*lo))
                numer = (b*hi*(weighted[l]-weighted[k])-a*(pref[l]-pref[k])
                         + b*(hi-lo)*(weighted[-1]-weighted[l]))
                assert numer>=0
                result[d] += numer*gn//(b*gd*(q-1)*p**e)
        nxt = [0]*(CAP_R+1)
        for j, mass in enumerate(R):
            if mass:
                for i, coef in enumerate(pm, start=1):
                    nxt[min(j*i,CAP_R)] += mass*coef//SCALE
        R = nxt
    return result


def initial_common(z, cap):
    values = [0]*cap
    for i in range(cap-1):
        pi = 1-z if i==0 else z-Q(2,9) if i==1 else Q(4,3**(i+1))
        for j in range(cap//(i+1)):
            d=(i+1)*(j+1)
            if d>=cap:
                break
            pj = 1-Q(4,15) if j==0 else Q(16,3*5**(j+1))
            values[d]+=down(SCALE*pi*pj)
    return values


def savings(omitted,z,joint_end,horizon):
    primes = [q for q in primes_through(horizon) if q>=11 and q!=omitted]
    schedule = steps(primes)
    joint = [p for p in primes if p<=joint_end]
    # Nondecreasing integer states past this cap never incur positive savings.
    cap = 1+max(down(schedule[p][0]) for p in joint)
    nu = initial_common(z,cap)
    total=0
    for i,p in enumerate(joint):
        t,g,_ = schedule[p]
        bs = local_B(p, primes[i+1:], schedule)
        nxt=[0]*cap
        zero = 1-g/p
        local = 0
        for d in range(1,cap):
            x=Q(d,p-1)
            kappa = 1/(1-x) if x<t/(p-1) else g
            if d<len(bs):
                local += down(nu[d]*(g-kappa)*min(Q(bs[d],SCALE),1/g))
            nxt[d] += down(nu[d]*zero)
            power=Q(p-1,p*p)
            for e in range(1,cap//d):
                if (e+1)*d>=cap:
                    break
                nxt[(e+1)*d] += down(nu[d]*kappa*power)
                power/=p
        nu=nxt
        total+=local
    return Q(total,SCALE)


def certify(omitted,joint_end,horizon,diagnostic):
    all_primes=primes_through(LIMIT)
    for z in [Q(5,9),Q(2,3)]:
        head=Q(4,3)*((1-z)/5+z/20+Q(1,12))
        pre,mid,tail=check_loss(all_primes,Q(2),Q(4,3),
            lambda *_:product_initial(None,None,z,Q(4,15)),
            minimum_prime=11,schedule=SCHEDULE,omit_stages=(omitted,))
        improvement=savings(omitted,z,joint_end,horizon)
        bound=head+pre+mid+tail-improvement
        print("omitted",omitted,"z",z,"local/marginal horizon",joint_end,horizon,
              "scalar",head+pre+mid+tail,"savings >=",improvement,
              "final upper",bound,"decimal",float(bound),flush=True)
        if not diagnostic:
            assert bound<1


if __name__=="__main__":
    parser=ArgumentParser()
    parser.add_argument("prime",type=int,choices=WINDOWS)
    parser.add_argument("--joint-end",type=int)
    parser.add_argument("--horizon",type=int)
    parser.add_argument("--diagnostic",action="store_true")
    args=parser.parse_args()
    p,h=WINDOWS[args.prime]
    certify(args.prime,args.joint_end or p,args.horizon or h,args.diagnostic)
