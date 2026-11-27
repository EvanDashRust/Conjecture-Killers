"""Constructive search on valuation boxes beyond the certified rank cut.
A sample cover only supplies a candidate. The recursive check is exact.
"""
import argparse
from functools import lru_cache
from itertools import combinations
import json
from math import isqrt, prod
from pathlib import Path

import numpy as np


def odd_primes(count):
    primes = []
    candidate = 3
    while len(primes) < count:
        if all(candidate % p for p in range(3, isqrt(candidate) + 1, 2)):
            primes.append(candidate)
        candidate += 2
    return primes


def coordinates(sizes, points, rng):
    return np.column_stack([rng.integers(size, size=points, dtype=np.int32) for size in sizes])


def candidate(sizes, samples, max_support, rng):
    remaining = coordinates(sizes, samples, rng)
    catalog = [support for k in range(2, max_support + 1)
               for support in combinations(range(len(sizes)), k)]
    catalog.sort(key=lambda support: prod(sizes[i] for i in support))
    patterns = []
    for support in catalog:
        if not len(remaining):
            break
        labels = np.zeros(len(remaining), dtype=np.int64)
        volume = 1
        for i in support:
            labels = labels * sizes[i] + remaining[:, i]
            volume *= sizes[i]
        if volume <= 500_000:
            counts = np.bincount(labels)
            choice = int(rng.choice(np.flatnonzero(counts == counts.max())))
        else:
            values, counts = np.unique(labels, return_counts=True)
            choice = int(rng.choice(values[counts == counts.max()]))
        pattern = [-1] * len(sizes)
        digits = choice
        for i in reversed(support):
            digits, pattern[i] = divmod(digits, sizes[i])
        patterns.append(pattern)
        remaining = remaining[labels != choice]
    return patterns, len(remaining)


def first_hole(sizes, patterns):
    rank = len(sizes)
    all_patterns = (1 << len(patterns)) - 1
    free = [all_patterns for _ in sizes]
    matches = [[0] * size for size in sizes]
    finished = [0] * rank
    for j, pattern in enumerate(patterns):
        bit = 1 << j
        last = -1
        for i, value in enumerate(pattern):
            if value >= 0:
                matches[i][value] |= bit
                free[i] ^= bit
                last = i
        assert last >= 0
        finished[last] |= bit

    @lru_cache(maxsize=100_000)
    def visit(i, mask):
        if not mask:
            return (0,) * (rank - i)
        options = [(mask & (free[i] | m), v) for v, m in enumerate(matches[i])]
        for new_mask, value in sorted(options, key=lambda item: item[0].bit_count()):
            if new_mask & finished[i]:
                continue
            suffix = visit(i + 1, new_mask)
            if suffix is not None:
                return (value,) + suffix
        return None

    return visit(0, all_patterns)


def point_misses(point, patterns):
    return all(any(p != -1 and p != v for p, v in zip(pattern, point)) for pattern in patterns)


def count_sample_misses(sizes, patterns, samples, rng):
    remaining = coordinates(sizes, samples, rng)
    for pattern in patterns:
        if not len(remaining):
            break
        hits = np.ones(len(remaining), dtype=bool)
        for i, value in enumerate(pattern):
            if value >= 0:
                hits &= remaining[:, i] == value
        remaining = remaining[~hits]
    return len(remaining)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--rank', type=int, default=20)
    parser.add_argument('--samples', type=int, default=200_000)
    parser.add_argument('--max-support', type=int, default=5)
    parser.add_argument('--seed', type=int, default=93)
    parser.add_argument('--output', type=Path, default=Path('candidate.json'))
    args = parser.parse_args()
    primes = odd_primes(args.rank)
    sizes = [p - 2 for p in primes]
    rng = np.random.default_rng(args.seed)
    patterns, training_misses = candidate(sizes, args.samples, args.max_support, rng)
    hole = first_hole(sizes, patterns)
    if hole is not None:
        assert point_misses(hole, patterns)
    report = {'primes': primes, 'sizes': sizes, 'seed': args.seed,
              'samples': args.samples, 'training_misses': training_misses,
              'holdout_misses': count_sample_misses(sizes, patterns, args.samples, rng),
              'uncovered_point': hole}
    print(json.dumps(report), flush=True)
    args.output.write_text(json.dumps(report | {'patterns': patterns}, separators=(',', ':')) + '\n')


if __name__ == '__main__':
    main()
