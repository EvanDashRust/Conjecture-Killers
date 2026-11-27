"""Exact arithmetic for the valuation-box exclusion. See PROOF.md."""
from fractions import Fraction as Q

# The first 18 primes above 3, in the order used by the sieve.
PRIMES = (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71)
DELTA = (Q(1, 9), Q(0), Q(1, 4), Q(1, 5), Q(3, 7), Q(3, 8), Q(3, 10),
         Q(1, 2), Q(1, 2), Q(7, 17), Q(7, 19), Q(7, 20), Q(7, 22), Q(1, 2),
         Q(1, 2), Q(1, 2), Q(15, 32), Q(15, 34))


def stage(size, delta, hits, zero_value, one_value):
    load = Q(2 * (2**hits - 1), size)
    cap = 1 / (1 - delta)
    adaptive_cap = 1 / (1 - min(load, delta))
    future_increment = (one_value - zero_value) / size
    return (cap * max(0, load - delta) + zero_value + cap * future_increment
            - (cap - adaptive_cap) * min(future_increment, 1 - delta))


def total(primes=PRIMES, schedule=DELTA):
    assert len(primes) == len(schedule)
    levels = list(zip(primes, schedule))
    bound = [Q(0)] * (len(levels) + 1)
    for index in range(len(levels) - 1, -1, -1):
        prime, delta = levels[index]
        size = prime - 3
        assert 0 <= delta <= Q(1, 2) and 1 / (1 - delta) <= size
        assert all(a <= b for a, b in zip(bound, bound[1:]))
        bound = [stage(size, delta, hits, bound[hits], bound[hits + 1])
                 for hits in range(index + 1)]
    return bound[0]


if __name__ == '__main__':
    result = total()
    assert result < Q(9991, 10000) < 1
    print('Exact upper bound below 9991/10000')
    print(f'Decimal approximation {float(result):.12f}')
