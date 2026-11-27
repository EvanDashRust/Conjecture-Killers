"""Exact finite separation of bounded slot repairs.

Unary and two-coordinate slots have their actual modes and are used at most
once. A higher phase is relaxed to any shallow triple, with repetition. Every
legal proposal at the same primes and heights is contained in this search.
"""
from functools import lru_cache
from itertools import combinations, product

from product_learning import phase


def repair_test(ps, hs, words, count, *, original=()):
    """Return None for an exclusion, or a list of relaxed additions.

    If original is supplied, retain its high-arity phases for free and remove
    an original unary or pair when its slot is changed. The input words must
    all escape the permanent high-arity phases. With original empty this
    tests coverage by additions alone.
    """
    if not words or count < 0:
        raise ValueError("Expected witnesses and a nonnegative edit budget")
    tables = {}
    shallow = []
    for i, (p, h) in enumerate(zip(ps, hs)):
        shallow.append((i, 1))
        for mode in range(1, h + 2):
            masks = {}
            for j, word in enumerate(words):
                v = phase(p, h, word[i], mode)
                masks[v] = masks.get(v, 0) | (1 << j)
            tables[i, mode] = masks
    groups = [(a,) for a in tables]
    groups.extend((a, b) for a, b in combinations(tables, 2) if a[0] != b[0])
    ids = {shape: i for i, shape in enumerate(groups)}
    full = (1 << len(words)) - 1
    # For fixed low-arity phases track *all* original hits on each word.
    signatures = [0] * len(words)
    for pattern in original:
        mask = full
        for i, e, v in pattern:
            mask &= tables[i, e].get(v, 0)
        if not mask:
            continue
        if len(pattern) > 2:
            raise ValueError("Window witness is covered by a permanent high-arity phase")
        bit = 1 << ids[tuple((i, e) for i, e, _ in pattern)]
        while mask:
            low = mask & -mask
            signatures[low.bit_length()-1] |= bit
            mask ^= low
    original_groups = {}
    for j, hits in enumerate(signatures):
        original_groups[hits] = original_groups.get(hits, 0) | (1 << j)

    @lru_cache(maxsize=None)
    def can_cover(left, available, remaining):
        active = 0
        for signature, mask in original_groups.items():
            if not signature & available:
                active |= mask
        active &= left
        if not active:
            return ()
        if not remaining:
            return None
        threshold = (active.bit_count() + remaining - 1) // remaining
        rich = {}
        options = []
        for a, masks in tables.items():
            large = []
            for name, mask in masks.items():
                hit = mask & active
                size = hit.bit_count()
                if size >= threshold:
                    large.append((name, mask, hit))
                    group = ids[a,]
                    if available & (1 << group):
                        options.append((size, mask, group, ((*a, name),)))
            if large:
                rich[a] = large
        for a, b in combinations(rich, 2):
            if a[0] == b[0]:
                continue
            group = ids[a,b]
            if not available & (1 << group):
                continue
            for (u, whole, hit), (v, cut, common) in product(rich[a], rich[b]):
                size = (hit & common).bit_count()
                if size >= threshold:
                    options.append((size, whole & cut, group, ((*a, u), (*b, v))))
        for a, b, c in combinations([key for key in shallow if key in rich], 3):
            for u, first, head in rich[a]:
                for v, second, middle in rich[b]:
                    both = head & middle
                    if both.bit_count() < threshold:
                        continue
                    for w, third, tail in rich[c]:
                        size = (both & tail).bit_count()
                        if size >= threshold:
                            options.append((size, first & second & third, None,
                                            ((*a, u), (*b, v), (*c, w))))
        for _, mask, group, pattern in sorted(options, key=lambda row: -row[0]):
            new_available = available if group is None else available ^ (1 << group)
            answer = can_cover(left & ~mask, new_available, remaining - 1)
            if answer is not None:
                return (pattern,) + answer
        return None

    answer = can_cover(full, (1 << len(groups)) - 1, count)
    return answer, can_cover.cache_info().currsize
