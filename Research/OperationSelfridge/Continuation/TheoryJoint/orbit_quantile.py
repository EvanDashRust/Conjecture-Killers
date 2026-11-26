"""Exact quantile distortion certificates for normalized odd covering heads without 7."""
from argparse import ArgumentParser
from bisect import bisect_right
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "Review"))
from joint_fibres import capped_exponent, ceiling, ceil_ratio, primes_through

SCALE = 10**20
PREFIX = 180_000
END = 10_000_000
THRESHOLDS = {11:3, 13:4, 17:4, 19:6, 29:8, 31:8, 37:12, 41:12,
              43:12, 47:16, 53:16, 59:16, 67:20, 71:24, 73:24}
MODS = (1, 3, 9, 5, 15, 45)
SHAPES = ((0,0), (0,0), (1,0), (0,1), (0,1), (1,1))
# (normalized orbit, omitted tail prime or 0, tested ordinary head gap,
# strict upper charge bound). Changing the head gap is legal only when
# an independent argument gives that much mass on the actual head holes.
CASES = {
    "square1lo": (1, 0, F(0), F(989,1000)),
    "square1hi": (1, 0, F(0), F(989,1000)),
    "square2": (2, 0, F(1,4), F(9999,10000)),
    "no23": (2, 23, F(1,4), F(9974,10000)),
    "no29ternary": (2, 29, F(139,540), F(992,1000)),
    "no31ternary": (2, 31, F(139,540), F(9996,10000)),
    "no29root": (2, 29, F(79,300), F(9973,10000)),
    "no29": (2, 29, F(53,200), F(9977,10000)),
    "no31": (2, 31, F(27,100), F(994,1000)),
    "no37": (2, 37, F(111,400), F(996,1000)),
    "head1": (1, 0, F(33,100), F(989,1000)),
    "head2": (2, 0, F(31,100), F(993,1000)),
}


def maxima_by_size(orbit, conditioned=0):
    cells = [x for x in range(45) if x%3 and x%5 and x%9 != orbit and x%15 != 1]
    n = len(cells)
    assert n == (18 if orbit==1 else 17)
    masks = [set(sum(1<<i for i,x in enumerate(cells) if x%m == b) for b in range(m))
             for m in MODS]
    if conditioned==25:
        weights = [3 if x%5==1 else 4 for x in cells]
    elif conditioned==27:
        weights = [1 if x%9==1 else 2 for x in cells]
    else:
        weights = [1]*n
    size = [0]*(1<<n)
    for subset in range(1,1<<n):
        bit = subset & -subset
        size[subset] = size[subset-bit]+weights[bit.bit_length()-1]
    strata = [set() for _ in range(sum(weights)+1)]
    for subset in range(1<<n):
        maxima = tuple(max(size[subset & mask] for mask in group) for group in masks)
        strata[size[subset]].add(maxima)
    return strata


def lower_hinge_atoms(strata, a_range=range(1,11), b_range=range(1,11), denominator=None):
    # For fixed upper exponents the dual envelope is a convex maximum of lines
    # after subtracting its true (uncapped) mean minus the test threshold.
    n = len(strata)-1
    atoms = defaultdict(F)
    pm3, pm5 = [capped_exponent(p, F(1)) for p in (3,5)]
    if denominator is None:
        denominator = n
    for a,b in product(a_range, b_range):
        weight = (1,1,a,b,b,a*b)
        best = [max(sum(x*y for x,y in zip(v,weight)) for v in vs) if vs else None for vs in strata]
        slopes, starts = [], []
        for j in range(n+1):
            if best[n-j] is None:
                continue
            while slopes:
                k = slopes[-1]
                x = F(best[n-k]-best[n-j], j-k)
                if len(slopes)==1 or x>starts[-1]:
                    break
                slopes.pop()
                starts.pop()
            slopes.append(j)
            starts.append(x if j else F(0))
        for i in range(1,len(slopes)):
            x = starts[i]
            assert x >= 0
            atoms[x] += pm3[a-1]*pm5[b-1]*F(slopes[i]-slopes[i-1],denominator)
    assert sum(atoms.values()) == F(n,denominator)*sum(pm3[a-1] for a in a_range)*sum(pm5[b-1] for b in b_range)
    return sorted(atoms.items())


def head(orbit, density, conditioned=0):
    strata = maxima_by_size(orbit)
    n = len(strata)-1
    s = density*45/n
    (maxima,) = strata[n]
    def moments(p):
        r = F(p-1)
        return (1, 1+1/r, 1+2/r+(p+1)/r**2, 1+(7*p*p-2*p+1)/r**3)
    m3, m5 = moments(3), moments(5)
    mean = sum(F(v,n)*m3[a]*m5[b] for v,(a,b) in zip(maxima,SHAPES))
    cube = F(0)
    for k in range(1,n+1):
        active = [shape for shape,v in zip(SHAPES,maxima) if k<=v]
        for triple in product(active, repeat=3):
            cube += F(m3[sum(a for a,_ in triple)] * m5[sum(b for _,b in triple)], n)
    if conditioned:
        # Removing one higher digit only reduces the *unnormalized*
        # comparison weights of exponent zero on the affected low cells.
        is_three = conditioned==27
        p = 3 if is_three else 5
        base = 1-F(1,p)
        weighted = maxima_by_size(orbit, conditioned)
        (weighted_maxima,) = weighted[-1]
        for mod,weighted_mod,(a,b) in zip(maxima,weighted_maxima,SHAPES):
            unrestricted = m5[b] if is_three else m3[a]
            mean += base*unrestricted*(F(weighted_mod,(p-1)*n)-F(mod,n))
        all_values = range(1,11)
        nonzero = range(2,11)
        before = (nonzero,all_values) if is_three else (all_values,nonzero)
        at_zero = ([1],all_values) if is_three else (all_values,[1])
        combined = defaultdict(F, lower_hinge_atoms(strata,*before))
        for x,w in lower_hinge_atoms(weighted,*at_zero,denominator=(p-1)*n):
            combined[x] += w
        atoms = sorted(combined.items())
    else:
        atoms = lower_hinge_atoms(strata)
    total = sum(w for _,w in atoms)
    cum = F(0)
    for u,w in atoms:
        cum += w
        if cum >= total-s:
            break
    correction = sum(max(u-x,0)*w for x,w in atoms)
    adjusted_mean = mean+correction-(total-s)*u
    # The positive-part envelope after upper-tail selection has lower-hinge
    # correction equal to that of the cap law after removing its lowest total-s.
    below = sum(w for x,w in atoms if x<u)
    at = dict(atoms)[u]
    assert below <= total-s <= below+at
    retained = [(u, below+at-(total-s))]+[(x,w) for x,w in atoms if x>u]
    assert sum(w for _,w in retained)==s
    return s, u, adjusted_mean, cube, retained


def product_endpoint(z):
    # Alternative/README.md derives this orbit-1 endpoint comparison.
    # Here all pure powers of 3 and 5 are allowed.
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "Alternative"))
    from power_orbits import coordinate
    v3, e3, c3 = coordinate(3, None, z)
    v5, e5, c5 = coordinate(5, None, F(4,15))
    distribution = defaultdict(F)
    for a,pa in enumerate(v3,1):
        for b,pb in enumerate(v5,1):
            distribution[F(a*b)] += pa*pb
    assert sum(distribution.values()) == 1
    mixed = F(4,3)*(F(1,12)+(1-z)/5+z/20)
    return (F(1),F(1),e3*e5,c3*c5,sorted(distribution.items())), mixed


def certify(case):
    orbit, omitted, density, target = CASES[case]
    conditioned = {"no29root":25, "no29ternary":27, "no31ternary":27}.get(case,0)
    prefix_limit = 600_000 if case=="no31ternary" else PREFIX
    mixed_head_cost = F(0)
    squarefree_through = 0
    if case in ("square1lo","square1hi"):
        z = F(5,9) if case=="square1lo" else F(2,3)
        inputs, mixed_head_cost = product_endpoint(z)
        squarefree_through = 13
    else:
        inputs = head(orbit, density, conditioned)
        if case=="square2":
            squarefree_through = 23
    s, u, mean0, cube, retained = inputs
    # Integer breakpoint grid shared by all rational atoms of the lower hinge.
    from math import lcm
    grid = lcm(*(x.denominator for x,_ in retained))
    xs, masses, offsets = [], [], []
    mass = off = F(0)
    for x,w in retained:
        mass += w
        off += w*x
        xs.append(int(x*grid))
        masses.append(ceiling(SCALE*mass))
        gross = SCALE*off
        offsets.append(gross.numerator//gross.denominator)
    assert u>=1 and len(xs)>0 and 0<s<=1
    print(case,'selected mass',s,'threshold',u,'mean upper input',mean0,'unconditional head third moment',cube,
          'retained breakpoints',len(xs),'grid',grid,flush=True)
    primes = primes_through(END)
    assert len(primes)-1==664578
    # All stored histograms are componentwise upper bounds on the exact
    # capped product law. Integers above high can never contribute again.
    high = 3*prefix_limit//10
    keys = []
    for i in range(1,high+1):
        m = i
        for q in (2,3,5,7):
            while m%q==0:
                m//=q
        if m==1:
            keys.append(i)
    index = {v:i for i,v in enumerate(keys)}
    links = [[index[j*v] for v in keys if j*v<=high] for j in range(1,11)]
    hist = [0]*len(keys)
    hist[0]=SCALE
    mean = SCALE
    cubic = ceiling(SCALE*cube)
    prefix = middle = 0
    for p in primes:
        if p<11 or p==omitted:
            continue
        only_first_power = p<=squarefree_through
        r = p if only_first_power else p-1
        ta = 10*THRESHOLDS[p] if p in THRESHOLDS else 3*r
        gamma = F(10*r, 10*r-ta)
        gn,gd=gamma.as_integer_ratio()
        if p<=prefix_limit:
            # Compute E[(t-ZY)_+] for the retained subprobability Y and
            # capped rough product Z. The inner quantity decreases in Z.
            correction = 0
            for z,v in zip(keys,hist):
                if 10*z*u.numerator >= ta*u.denominator:
                    break
                if not v:
                    continue
                k = bisect_right(xs, ta*grid//(10*z))-1
                if k>=0:
                    upper = ta*masses[k] - 10*z*offsets[k]
                    assert upper>=0
                    correction += ceil_ratio(v*upper,SCALE)
            # 10 times the first moment subtraction in units of SCALE.
            raw = ceiling(10*mean*mean0 - ta*s*SCALE) + correction
            assert raw>=0
            prefix += ceil_ratio(raw*gn,10*r*gd)
            nxt = [0]*len(hist)
            probabilities = ([1-gamma/p,gamma/p] if only_first_power
                             else capped_exponent(p,gamma))
            for link,prob in zip(links,probabilities):
                coeff=ceiling(prob*SCALE)
                for i,k in enumerate(link):
                    if hist[i]:
                        nxt[k] += ceil_ratio(hist[i]*coeff,SCALE)
            hist = nxt
            mean += ceil_ratio(mean*gn,gd*r)
        else:
            middle += ceil_ratio(4000*cubic,1701*r**3)
        if only_first_power:
            cubic += ceil_ratio(7*cubic*gn,gd*p)
        else:
            cubic += ceil_ratio(cubic*gn*(7*p*p-2*p+1),gd*r**3)
    b = len(primes)-1
    assert F(11,4)**13 < b
    infinite = F(4000*cubic,1701*SCALE*b*b*13**2*14)
    if squarefree_through:
        print('squarefree rough primes through',squarefree_through,
              'mixed pure-coordinate head charge',mixed_head_cost)
    loss=mixed_head_cost+F(prefix+middle,SCALE)+infinite
    print('prefix',F(prefix,SCALE),'middle',F(middle,SCALE),'infinite',infinite)
    print('upper total charge 1-s+loss',float(1-s+loss))
    print('lower mass margin (relative to the initial low cells)',float(s-loss))
    assert 1-s+loss<target

if __name__=='__main__':
    parser = ArgumentParser()
    parser.add_argument('case', nargs='?', choices=CASES, default='no23')
    certify(parser.parse_args().case)
