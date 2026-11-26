"""Exact hole products for the fixed-prime, fixed-height released catalogue.

Each coordinate holds its actual (low root, first nonzero digit) pairs.
No arithmetic lift, SAT solver or floating-point calculation is used here.
"""
from functools import lru_cache
from itertools import product
from math import gcd, prod
from random import Random


def alphabets(ps, hs):
    if len(ps) != len(hs):
        raise ValueError("Unpaired primes and heights")
    return tuple(tuple(product(range(p**h), range(1, p))) for p, h in zip(ps, hs))


def phase(p, h, atom, mode):
    root, digit = atom
    return root * (p - 1) + digit - 1 if mode == h + 1 else root % p**mode


class PatternIndex:
    """Coordinate bitsets of the patterns accepting each individual atom."""

    def __init__(self, ps, hs, patterns):
        self.alph = alphabets(ps, hs)
        self.rank = len(ps)
        self.all = (1 << len(patterns)) - 1
        self.end = [0] * self.rank
        self.touched = [0] * self.rank
        groups = [dict() for _ in ps]
        for number, pattern in enumerate(patterns):
            bit = 1 << number
            self.end[max(i for i, _, _ in pattern)] |= bit
            for i, mode, v in pattern:
                self.touched[i] |= bit
                key = mode, v
                groups[i][key] = groups[i].get(key, 0) | bit
        self.accept = []
        for i, (p, h, axis) in enumerate(zip(ps, hs, self.alph)):
            unconstrained = self.all ^ self.touched[i]
            lut = {}
            for atom in axis:
                mask = unconstrained
                for mode in range(1, h + 2):
                    mask |= groups[i].get((mode, phase(p, h, atom, mode)), 0)
                lut[atom] = mask
            self.accept.append(lut)

    def _box(self, box):
        if len(box) != self.rank:
            raise ValueError("Box has wrong rank")
        box = tuple(tuple(map(tuple, axis)) for axis in box)
        for i, axis in enumerate(box):
            if not axis or len(axis) != len(set(axis)) or not set(axis) <= self.accept[i].keys():
                raise ValueError(f"Invalid atom set on coordinate {i}")
        return box

    def intersection(self, box):
        """Rows intersecting the entire product as sets, including partial intersections."""
        active = self.all
        for i, axis in enumerate(self._box(box)):
            meet = 0
            for atom in axis:
                meet |= self.accept[i][atom]
            active &= meet
        return active

    def grow(self, word, order=None):
        word = tuple(map(tuple, word))
        box = list(self._box([(atom,) for atom in word]))
        if self.intersection(box):
            raise ValueError("Seed meets a pattern")
        order = list(range(self.rank) if order is None else order)
        if sorted(order) != list(range(self.rank)):
            raise ValueError("Expected a coordinate permutation")
        possible = [self.accept[i][atom] for i, atom in enumerate(word)]
        for i in order:
            relevant = self.all
            for j, mask in enumerate(possible):
                if i != j:
                    relevant &= mask
            axis = tuple(atom for atom in self.alph[i] if not relevant & self.accept[i][atom])
            box[i] = axis
            possible[i] = 0
            for atom in axis:
                possible[i] |= self.accept[i][atom]
        if self.intersection(box):
            raise AssertionError("Constructed product intersects a pattern")
        return tuple(box)

    def hole(self, box):
        box = self._box(box)

        @lru_cache(maxsize=100000)
        def search(i, active):
            if not active:
                return tuple(axis[0] for axis in box[i:])
            # Equal surviving pattern sets induce exactly the same suffix problem.
            choices = {}
            for atom in box[i]:
                surviving = active & self.accept[i][atom]
                if not surviving & self.end[i]:
                    choices.setdefault(surviving, atom)
            for surviving in sorted(choices, key=int.bit_count):
                suffix = search(i + 1, surviving)
                if suffix is not None:
                    return (choices[surviving],) + suffix
            return None

        return search(0, self.all)


def hole_product(ps, hs, patterns, word, order=None):
    return PatternIndex(ps, hs, patterns).grow(word, order)


def verify_product(ps, hs, patterns, box):
    """Returns the exact number of certified escaping words, or raises."""
    index = PatternIndex(ps, hs, patterns)
    if index.intersection(box):
        raise ValueError("Product meets an assigned pattern")
    return prod(map(len, box))


def family_hole(ps, hs, patterns, box):
    """A word in the family missed by the *union*, or None iff all are covered."""
    return PatternIndex(ps, hs, patterns).hole(box)


def slice_batch(box, word, limit=128, seed=0):
    """A bounded list of distinct points in a certified product including the seed."""
    box = tuple(tuple(map(tuple, axis)) for axis in box)
    word = tuple(map(tuple, word))
    if len(word) != len(box) or not all(atom in axis for atom, axis in zip(word, box)):
        raise ValueError("Seed is outside box")
    if limit < 1:
        raise ValueError("Batch limit must include seed")
    words = {word: None}
    # Spread point constraints over the product after one small-prime line.
    i = next((i for i, axis in enumerate(box) if len(axis) > 1), 0)
    for atom in box[i]:
        if len(words) >= max(1, limit // 2):
            break
        words[word[:i] + (atom,) + word[i+1:]] = None
    size = prod(map(len, box))
    rng = Random(seed)
    pos = rng.randrange(size)
    step = rng.randrange(1, size) if size > 1 else 1
    while gcd(step, size) != 1:
        step += 1
    while len(words) < min(limit, size):
        k = pos
        digits = []
        for axis in box:
            k, residue = divmod(k, len(axis))
            digits.append(axis[residue])
        words[tuple(digits)] = None
        pos = (pos + step) % size
    return tuple(words)
