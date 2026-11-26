"""Integer bounds for the finite-rank, complete-column joint distortion recursion."""
from fractions import Fraction as Q
from pathlib import Path
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'TheoryJoint'))
from orbit_quantile import head, primes_through

SCALE = 10**20
EXIT = 14


def up(n, d):
    return -(-n // d)


def backward(primes, thresholds):
    """At integral input m > limit the exact continuation is affine."""
    limit = max(thresholds) + 1
    cost = [0] * (limit + 1)
    slope = intercept = 0
    for p, t in reversed(list(zip(primes, thresholds))):
        r = p - 1
        assert 0 <= 2*t <= r
        # c=r/(r-t). A*m-B bounds the exact affine branch at the right.
        # On the entire half-line A*m bounds the true continuation.
        affine = lambda m: slope*m - intercept
        unit = p**(EXIT-1)*r
        weights = [r*r * p**(EXIT-1-j) for j in range(2, EXIT)]
        future = [0]*(limit+1)
        for m in range(1, limit+1):
            # Positive exponent part of K_1. At 1+T >= EXIT the first
            # moment is exact, and slope*m*(1+T) bounds every cost there.
            mass = slope*m*(EXIT*r+1)
            for j, w in enumerate(weights, 2):
                v = m*j
                mass += w * (cost[v] if v <= limit else affine(v))
            b = Q(mass - (unit//p)*cost[m], unit)
            c = Q(r, r-t)
            kappa = c if m >= t else Q(r, r-m)
            adjusted = max(kappa*b, c*b - SCALE*(c-kappa)/c)
            value = cost[m] + adjusted + SCALE*Q(max(0,m-t), r-t)
            future[m] = up(value.numerator, value.denominator)
        slope = up(slope*(r-t+1) + SCALE, r-t)
        intercept += SCALE*t // (r-t)
        cost = future

    def upper(x):
        lo = x.numerator // x.denominator
        def at(m):
            return cost[m] if m <= limit else slope*m - intercept
        # Convexity of the *mathematical* continuation gives the chord.
        return Q(at(lo) + (x-lo)*(at(lo+1)-at(lo)), SCALE)
    return Q(slope,SCALE), upper


def product_head(z, slope, upper):
    g5 = Q(4,3)
    # Law of min(T,18). Higher exponents are paid via the global slope.
    def pmf(p,g,a):
        tails = [Q(1), a]+[g/p**e for e in range(2,19)]+[Q(0)]
        return [a-b for a,b in zip(tails,tails[1:])]
    p3, p5 = pmf(3,Q(2),z), pmf(5,g5,g5/5)
    smooth = g5*((1-z)/5 + z/20 + Q(1,12))
    mean = (1+z+Q(1,3))*(1+g5/4)
    for i,pi in enumerate(p3,1):
        for j,pj in enumerate(p5,1):
            smooth += pi*pj*(upper(Q(i*j))-slope*i*j)
    return smooth+slope*mean


def certify(orbit, thresholds):
    primes = [p for p in primes_through(5000) if p >= 11][:len(thresholds)]
    assert len(primes) == len(thresholds)
    slope, upper = backward(primes, thresholds)
    if orbit == 1:
        charges = [product_head(z,slope,upper) for z in (Q(5,9),Q(2,3))]
    else:
        mass, _, adjusted_mean, _, atoms = head(2, Q(1,4))
        assert mass == Q(45,68)
        error = adjusted_mean - sum(y*w for y,w in atoms)
        assert 0 <= error < Q(1,100000)
        charges = [1-mass+sum(w*upper(y) for y,w in atoms)+slope*error]
    for value in charges:
        print('orbit',orbit,'rank at most',len(primes)+2,'last prime',primes[-1],
              'upper numerator over 10^12', up(value.numerator*10**12,value.denominator),
              flush=True)
        assert value < 1


if __name__ == '__main__':
    for key, schedule in json.loads((HERE/'schedules.json').read_text()).items():
        certify(int(key),schedule)
