"""Independently check that a saved valuation-box candidate has an exact hole."""
import json
from math import isqrt
from pathlib import Path
import sys


def check(path):
    data = json.loads(Path(path).read_text())
    primes, sizes = data['primes'], data['sizes']
    assert primes == sorted(set(primes))
    assert all(p >= 3 and p % 2 and all(p % d for d in range(2, isqrt(p) + 1)) for p in primes)
    assert sizes == [p - 2 for p in primes]
    point = data['uncovered_point']
    assert len(point) == len(sizes) and all(0 <= v < s for s, v in zip(sizes, point))
    used_supports = set()
    for pattern in data['patterns']:
        assert len(pattern) == len(sizes) and all(-1 <= v < s for s, v in zip(sizes, pattern))
        support = tuple(i for i, v in enumerate(pattern) if v >= 0)
        assert len(support) >= 2 and support not in used_supports
        used_supports.add(support)
        assert tuple(point[i] for i in support) != tuple(pattern[i] for i in support)
    print(f'The explicit point avoids all {len(used_supports)} patterns.')


if __name__ == '__main__':
    check(sys.argv[1] if len(sys.argv) > 1 else 'rank20_candidate.json')
