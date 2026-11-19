#!/usr/bin/env python3
"""Independent exact-integer regression check; finite evidence, not a proof.

Usage: python3 experiments/exact.py 100
"""
import sys

N = int(sys.argv[1]) if len(sys.argv) > 1 else 100
if N < 1:
    raise ValueError("N must be positive")
S = [[0] * (N + 1) for _ in range(N + 1)]
S[0][0] = 1
for n in range(1, N + 1):
    for k in range(1, n + 1):
        S[n][k] = S[n - 1][k - 1] + k * S[n - 1][k]

num_equal = num_strict = 0
for n in range(1, N + 1):
    for p in range(1, n + 1):
        for j in range(1, p + 1):
            lhs = S[p - 1][j - 1] * S[n - 1][p - 1] * S[n][j]
            rhs = S[p][j] * S[n][p] * S[n - 1][j - 1]
            if lhs < rhs:
                raise AssertionError(f"counterexample: (n,p,j)=({n},{p},{j})")
            on_boundary = j == 1 or p == j or p == n
            if lhs == rhs:
                assert on_boundary, (n, p, j)
                num_equal += 1
            else:
                assert not on_boundary, (n, p, j)
                num_strict += 1
print(f"n <= {N}: {num_equal + num_strict:,} triples, "
      f"{num_equal:,} equalities, {num_strict:,} strict inequalities, zero counterexamples")
