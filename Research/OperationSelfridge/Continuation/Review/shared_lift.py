"""Independent single-auxiliary lift and compact concrete hole certificates."""
import argparse
import json
from itertools import product
from math import gcd, isqrt, lcm, prod


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def crt(pairs):
    """Merge equations iteratively. Inputs have coprime positive moduli."""
    modulus, residue = 1, 0
    for m, a in pairs:
        delta = (a - residue) * pow(modulus, -1, m) % m
        residue += modulus * delta
        modulus *= m
    return modulus, residue


def setup(primes, heights, patterns, auxiliary, allow_even=False):
    if not primes or len(primes) != len(heights) or len(set(primes)) != len(primes):
        raise ValueError("Invalid coordinate list")
    if not prime(auxiliary) or auxiliary % 2 == 0 or auxiliary in primes:
        raise ValueError("The common auxiliary must be a fresh odd prime")
    if any(not prime(p) or (not allow_even and p % 2 == 0) for p in primes):
        raise ValueError("Invalid core prime")
    if any(type(h) is not int or h < 0 for h in heights):
        raise ValueError("Invalid prefix height")
    shapes = set()
    for pattern in patterns:
        coords = [i for i, _, _ in pattern]
        if not coords or len(coords) != len(set(coords)):
            raise ValueError("Invalid pattern")
        shape = tuple(sorted((i, e) for i, e, _ in pattern))
        if shape in shapes:
            raise ValueError("Repeated mode vector")
        shapes.add(shape)
        for i, e, a in pattern:
            if not 0 <= i < len(primes):
                raise ValueError("Invalid index")
            p, h = primes[i], heights[i]
            if not 1 <= e <= h + 1:
                raise ValueError("Invalid mode")
            limit = p**e if e <= h else p**h * (p - 1)
            if not 0 <= a < limit:
                raise ValueError("Invalid assignment")


def assigned(h, r, q, j):
    """For each prime, distinct (root,phase) give distinct labels above h."""
    return h + (q - 1) * r + j


def classes(primes, heights, patterns, q):
    """Includes auxiliaries for every root, keeping them fixed across candidate updates."""
    yield q, 0
    for p, h in zip(primes, heights):
        for r in range(p**h):
            for j in range(1, q):
                yield crt(((q, j), (p**assigned(h, r, q, j), r)))
    for pattern in patterns:
        choices = []
        for i, e, a in pattern:
            p, h = primes[i], heights[i]
            if e <= h:
                choices.append(((p**e, a),))
            else:
                root, digit0 = divmod(a, p - 1)
                top = assigned(h, root, q, q - 1)
                choices.append(tuple((p**(k + 1), root + (digit0 + 1)*p**k)
                                     for k in range(h, top)))
        for factors in product(*choices):
            yield crt(factors)


def integer_hole(primes, heights, patterns, q, word):
    """Realize first exits at exactly h. No expanded family enumeration is needed."""
    if len(word) != len(primes):
        raise ValueError("Invalid witness length")
    congruences = [(q, q - 1)]
    for p, h, (r, d) in zip(primes, heights, word):
        if not 0 <= r < p**h or not 1 <= d < p:
            raise ValueError("Invalid atom")
        congruences.append((p**(h + 1), r + d * p**h))
    _, x = crt(congruences)
    for p, h in zip(primes, heights):
        r = x % p**h
        # With auxiliary residue -1, the only potentially active auxiliary for
        # this coordinate is at this root. It fails already at exponent h + 1.
        assert x % p**(h+1) != r
        assert assigned(h, r, q, q - 1) >= h + 1
    for pattern in patterns:
        for i, e, phase in pattern:
            p, h = primes[i], heights[i]
            if e <= h:
                if x % p**e != phase:
                    break
            else:
                root, digit0 = divmod(phase, p - 1)
                if x % p**(h+1) != root + (digit0 + 1)*p**h:
                    break
        else:
            raise ValueError("Point matches a pattern")
    return x


def counts(primes, heights, patterns, q):
    """Return the exact number of lifted classes, and counts at each prime."""
    aux = 1 + (q-1)*sum(p**h for p, h in zip(primes, heights))
    total = aux
    divisible = {p: (q-1)*p**h for p, h in zip(primes, heights)}
    divisible[q] = aux
    for pattern in patterns:
        copies = 1
        for i, e, a in pattern:
            p, h = primes[i], heights[i]
            if e > h:
                r = a // (p-1)
                copies *= assigned(h,r,q,q-1)-h
        total += copies
        for i, _, _ in pattern:
            divisible[primes[i]] += copies
    return total, divisible


def terminal_classes(q, rectangles):
    """rectangles contains (period, residue, q-1 allocated nontrivial divisors)."""
    if not prime(q) or q % 2 == 0:
        raise ValueError("Terminal modulus must be an odd prime")
    used = set()
    yield q, 0
    for period, residue, divisors in rectangles:
        if period <= 0 or period % 2 == 0 or gcd(period,q) != 1 or len(divisors) != q-1:
            raise ValueError("Invalid terminal")
        for j, d in enumerate(divisors, 1):
            if d <= 1 or period % d or d in used:
                raise ValueError("Divisor must be available")
            used.add(d)
            yield crt(((q,j), (d,residue)))


def controls():
    # The fixed unary at prime 2 covers the even root. On its odd root the
    # variable digit at 3 selects the unary at 3 or the joint variable mode.
    ps, hs, q = [2,3], [1,0], 5
    pats = [[(0,1,0)], [(1,1,1)], [(0,2,1), (1,1,0)]]
    setup(ps,hs,pats,q,allow_even=True)
    realized = list(classes(ps,hs,pats,q))
    assert len(realized) == len({m for m,_ in realized})
    total, divisibility = counts(ps, hs, pats, q)
    assert total == len(realized)
    assert all(count == sum(m%p == 0 for m,_ in realized) for p,count in divisibility.items())
    period = lcm(*(m for m,_ in realized))
    assert all(any(x%m == a for m,a in realized) for x in range(period))
    for delete,word in ((0,[(0,1),(0,1)]), (1,[(1,1),(0,2)]), (2,[(1,1),(0,1)])):
        candidate = [pat for j,pat in enumerate(pats) if j != delete]
        x = integer_hole(ps,hs,candidate,q,word)
        assert all(x%m != a for m,a in classes(ps,hs,candidate,q))
    rectangles=[(35,4,(5,7)),(385,9,(11,35))]
    terms=list(terminal_classes(3,rectangles))
    assert len(terms) == len({m for m,_ in terms})
    for x in range(lcm(3,*(m for m,_,_ in rectangles))):
        if any(x%m == a for m,a,_ in rectangles):
            assert any(x%m == a for m,a in terms)
    print("Complete mixed control:", total,"classes, period",period)
    print("Three deletion witnesses and two shared terminal rectangles verified.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("candidate", nargs="?")
    args = parser.parse_args()
    controls()
    if args.candidate:
        with open(args.candidate) as handle:
            data = json.load(handle)
        if data.get("terminal"):
            raise ValueError("Separate terminal gadget must be checked for this candidate.")
        ps,hs = data["primes"],data["heights"]
        pats = data["pure"] + data["patterns"]
        q = 3
        while not prime(q) or q in ps:
            q += 2
        setup(ps,hs,pats,q)
        x = integer_hole(ps,hs,pats,q,data["uncovered_atom_word"])
        total,divisible = counts(ps,hs,pats,q)
        print(json.dumps({"shared_auxiliary":q,"integer_hole":str(x),
                          "actual_classes":total,"divisible_by":divisible}))
