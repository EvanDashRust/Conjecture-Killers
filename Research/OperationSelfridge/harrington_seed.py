"""Explicit reconstruction of Harrington's distinct near-cover.
Adapted from the valuation presentation cited in PROOF.md. Pairs are (modulus, residue).
"""
from math import prod


def crt(*pairs):
    modulus = prod(m for m, _ in pairs)
    residue = sum(a * (modulus // m) * pow(modulus // m, -1, m) for m, a in pairs)
    return modulus, residue % modulus


def seed():
    yield 3, 1
    for n in range(1, 16):
        yield 3**(n + 1), 3**n
    for s in range(12):
        p5 = 5**(s + 1)
        yield p5, 5**s
        yield crt((3, 0), (p5, 2 * 5**s))
        for n in range(1, 16):
            yield crt((3**(n + 1), 2 * 3**n), (p5, 3 * 5**s))
    for u in range(10):
        p7 = 7**(u + 1)
        yield p7, 7**u
        yield crt((3, 0), (p7, 2 * 7**u))
        for s in range(12):
            p5 = 5**(s + 1)
            yield crt((p5, 4 * 5**s), (p7, 3 * 7**u))
            yield crt((3, 0), (p5, 4 * 5**s), (p7, 4 * 7**u))
        for n in range(1, 16):
            p3 = 3**(n + 1)
            yield crt((p3, 2 * 3**n), (p7, 5 * 7**u))
            for s in range(12):
                yield crt((p3, 2 * 3**n), (5**(s + 1), 4 * 5**s), (p7, 6 * 7**u))
    for p, q in [(7, 11), (5, 13), (3, 17)]:
        yield q, 0
        for j in range(1, q):
            yield crt((p**j, 0), (q, j))


WITNESS = {
    3: (3, {2}),
    5: (25, {x for x in range(25) if x % 5 in {2, 3, 4} or x in {10, 15, 20}}),
    7: (49, {x for x in range(49) if x % 7 in {2, 4, 5, 6} or x in {14, 28, 35, 42}}),
    11: (11, set(range(2, 11))),
    13: (13, set(range(2, 13))),
    17: (17, set(range(1, 17))),
}


def meets_witness(modulus, residue):
    from math import gcd
    return all(any((x - residue) % gcd(modulus, period) == 0 for x in values)
               for period, values in WITNESS.values())


def verify():
    classes = list(seed())
    assert len(classes) == len({m for m, _ in classes}) == 2471
    assert all(m > 1 and m % 2 and 0 <= a < m for m, a in classes)
    assert all(not meets_witness(m, a) for m, a in classes)
    assert meets_witness(3, 2)  # Positive intersection control.
    print('All 2471 Harrington classes miss the product witness, by exact CRT checks.')


if __name__ == '__main__':
    verify()
