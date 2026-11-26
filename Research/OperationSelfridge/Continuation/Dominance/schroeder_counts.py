"""Restore exceptions in the two full-period measures of Schroeder (2026)."""
from fractions import Fraction as F
from math import prod
from arity_tail import primes

THRESHOLDS = {
    3:F(0), 5:F(0), 7:F(1,5), 11:F(1,3), 13:F(6,11), 17:F(29,50),
    19:F(11,17), 23:F(16,25), 29:F(19,27), 31:F(18,25),
    37:F(37,50), 41:F(29,39), 43:F(31,41), 47:F(34,45),
    53:F(19,25), 59:F(37,50), 61:F(37,50)
}


def cap(p):
    return F(p-1,p-2) / (1-THRESHOLDS.get(p,F(1,2)))


def main():
    # At p>=67 the cap decreases to 2; all other factors are checked directly.
    assert cap(67)**2 < 67
    assert all(cap(p)**2 <= p for p in THRESHOLDS if p != 3)
    assert cap(3)**2 == 4
    limit = 1_000_000
    small = primes(200)
    weights = []
    min_weight = F(1,700)
    # Beyond this cutoff even the square-root cap lies below the selection floor.
    assert F(4,3*limit) < min_weight**2
    # Split the modulus by its largest prime. If p>=200, the other three
    # or more first-power cap factors have product at most their largest three.
    first_three = sorted((cap(p)/p for p in small if p>2), reverse=True)[:3]
    assert cap(211)/211 < first_three[-1]
    largest_three = prod(first_three)
    assert largest_three * cap(211)/211 < min_weight
    # 199 is followed by 211. For larger p the ratio cap(p)/p decreases.
    assert primes(212)[-2:] == [199,211]
    def visit(n, factors, weight, start):
        if factors >= 4:
            weights.append(weight)
        for i in range(start, len(small)):
            p = small[i]
            m, w = n*p, weight*cap(p)/p
            while m <= limit and w >= min_weight:
                visit(m, factors+1, w, i+1)
                m *= p
                w /= p
    visit(1,0,F(1),1)
    weights.sort(reverse=True)
    for margin in (F(62924,10**6),F(26213,10**6)):
        cumulative = F(0)
        for n, w in enumerate(weights,1):
            if cumulative+w >= margin:
                print('missed mass >',margin,'at least',n,
                      'previous sum',cumulative,'threshold weight',w)
                break
            cumulative += w
        else:
            raise AssertionError('Enumeration floor too high')


if __name__ == '__main__':
    main()
