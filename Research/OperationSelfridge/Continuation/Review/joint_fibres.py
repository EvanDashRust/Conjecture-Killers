"""Exact cross-prime distortion certificate for omitted pure 3 or 9."""
from argparse import ArgumentParser
from fractions import Fraction as Q
from math import isqrt

UNIT = 10**20
LIMIT = 10_000_000
PREFIX = 60_000
CAP = 10
EARLY = {7: 2, 11: 2, 13: 3, 17: 4, 19: 4, 23: 6, 29: 6, 31: 8, 37: 8, 41: 8}


def primes_through(limit):
    mark = bytearray([1]) * (limit + 1)
    mark[:2] = bytes(2)
    for i in range(2, isqrt(limit) + 1):
        if mark[i]:
            mark[i*i::i] = bytes((limit-i*i)//i + 1)
    return [p for p in range(2, limit + 1) if mark[p]]


def ceiling(x):
    return -(-x.numerator // x.denominator)


def ceil_ratio(a, b):
    return -(-a // b)


def capped_exponent(p, gamma):
    # Distribution of min(T, CAP-1), with P(T>=j) = gamma/p^j.
    return ([1 - gamma / p]
            + [gamma * (p-1) / p**(j+1) for j in range(1, CAP-1)]
            + [gamma / p**(CAP-1)])


def moments(p, gamma):
    return (gamma / (p-1), gamma*(p+1)/(p-1)**2,
            gamma*(p*p+4*p+1)/(p-1)**3)


def head(g3, g5):
    # Head counts only divisors with no factor 15.
    distribution = {}
    for i, x in enumerate(capped_exponent(3, g3)):
        for j, y in enumerate(capped_exponent(5, g5)):
            key = 1+i+j
            distribution[key] = distribution.get(key, 0) + ceiling(UNIT*x*y)
    a1, a2, a3 = moments(3, g3)
    b1, b2, b3 = moments(5, g5)
    first = 1 + a1 + b1
    third = (1 + 3*(a1+b1) + 3*(a2+2*a1*b1+b2)
             + a3+3*a2*b1+3*a1*b2+b3)
    return distribution, ceiling(first*UNIT), ceiling(third*UNIT)


def check_loss(primes, g3, g5):
    hist, mean, cubic = head(g3, g5)
    high = 3*PREFIX//10
    prefix = middle = 0
    for p in primes:
        if p < 7:
            continue
        r = p-1
        delta = Q(EARLY[p], r) if p in EARLY else Q(3, 10)
        gamma = 1 / (1-delta)
        if p <= PREFIX:
            t = delta*r
            a, b = t.as_integer_ratio()
            correction = sum((a-b*n)*v for n, v in hist.items() if b*n < a)
            excess = b*mean - a*UNIT + correction
            prefix += ceil_ratio(gamma.numerator*excess, gamma.denominator*b*r)
            next_hist = {}
            for j, prob in enumerate(capped_exponent(p, gamma), start=1):
                coeff = ceiling(prob * UNIT)
                for n, v in hist.items():
                    m = j*n
                    if m <= high:
                        next_hist[m] = next_hist.get(m, 0) + ceil_ratio(coeff*v, UNIT)
            hist = next_hist
            mean = ceiling(mean*(1+gamma/r))
        else:
            middle += ceil_ratio(4000*cubic, 1701*r**3)
        cubic += ceil_ratio(cubic*gamma.numerator*(7*p*p-2*p+1), gamma.denominator*r**3)
    # Dai et al., Lemma 2.10, with beta=15, ell=13. The third moment
    # entering it is recomputed directly, with upward rounding.
    b = len(primes)-1
    assert b == 664578 and Q(11, 4)**13 < b
    tail = Q(4000*cubic, 1701*UNIT*b*b*13**2*14)
    return Q(prefix, UNIT), Q(middle, UNIT), tail


def mixed_weights(g3, g5):
    # For any odd prime except 3, gamma_q**4 <= q. At 3 allow
    # gamma_3**4 <= 3*3. Hence W(m)**4 <= 3/m**3.
    limit_d = 20_000
    factors = [Q(1)]*(limit_d+1)
    for p in primes_through(limit_d):
        if p == 2:
            continue
        if p == 3:
            gamma = g3
        elif p == 5:
            gamma = g5
        else:
            delta = Q(EARLY[p],p-1) if p in EARLY else Q(3,10)
            gamma = 1/(1-delta)
        assert gamma**4 <= p * (3 if p == 3 else 1)
        for m in range(p, limit_d+1, 2*p):
            factors[m] *= gamma
    return sorted(((factors[m]/m,m) for m in range(15,limit_d+1,30)),reverse=True), limit_d


def check(omitted):
    g3 = Q(6, 5) if omitted == 3 else Q(18, 11)
    g5 = Q(4, 3)
    prefix, middle, tail = check_loss(primes_through(LIMIT), g3, g5)
    survivor = 1 - prefix - middle - tail
    print('omitted', omitted)
    for name, qty in [('prefix', prefix), ('middle', middle), ('tail', tail), ('survivor', survivor)]:
        print(name, qty, float(qty))
    target = Q(204515, 1_000_000) if omitted == 3 else Q(7381, 1_000_000)
    assert survivor > target
    ranked, limit_d = mixed_weights(g3, g5)
    cases = [(set(),6), ({15},26), ({15,45},41), ({15,45,75},54)] if omitted == 3 else [(set(),1)]
    for forbidden, minimum in cases:
        total = 0
        for i, (w, m) in enumerate(((w,m) for w,m in ranked if m not in forbidden), start=1):
            if total+w >= target:
                break
            total += w
        assert i == minimum and total < target
        print('also absent', sorted(forbidden), 'count >=', i, 'previous weight', total)
        if i > 1:
            selected = [w for w,m in ranked if m not in forbidden][:i-1]
            assert min(selected)**4 * limit_d**3 > 3


if __name__ == '__main__':
    parser = ArgumentParser()
    parser.add_argument('omitted', type=int, choices=(3,9))
    check(parser.parse_args().omitted)
