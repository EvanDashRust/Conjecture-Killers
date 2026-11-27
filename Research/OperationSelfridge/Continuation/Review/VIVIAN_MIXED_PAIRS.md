# Operation Selfridge: a restricted exclusion that allows mixed fresh primes

**Conditional on retaining the 2,471-class Harrington seed reconstructed in Mabel's checkpoint 3** (Conjecture Killers draft PR #3), build a graph of fresh primes: two primes outside P={3,5,7,11,13,17} are adjacent if some added modulus contains both. A distinct odd completion of this seed must satisfy at least one:

* some connected component of this graph has at least three fresh primes; or
* some edge of this graph contains a prime at most 239.

This permits arbitrarily many fresh primes, arbitrary powers, and arbitrary mixed moduli within arbitrarily many separate two-prime blocks. It does not rule out a mixed component containing a small prime, a larger connected component, a changed Harrington seed, or an unrestricted solution of Erdős #7. The extension below was checked with exact rational arithmetic, not Lean; it builds on Mabel's head witness and convex comparison argument.

## Block load and avoidance

Use the old-prime product witness and the axis conditioning from checkpoint 3. Its old-only survivor probability is at least S=0.322332585347204393 (rounded down). The remaining six head coordinates have independent alignment comparison variables T_p, with P(T_p≥e) = 1/(s'_p p^(e−1)). The scalar comparison quantity is D=∏(1+T_p).

For a fresh block B, fix the head point x. Each added class whose nonempty fresh support lies in B consumes at most ∏ q^(−e_q) of the fresh-coordinate fibre if its head congruence matches x. Let L_B(x) be the sum of these fractions. If that block's fibre is entirely blocked, L_B(x)≥1. By the same coordinate alignment as in checkpoint 3, any convex increasing payoff of L_B has expectation at most that of D times A_B, where
    A_B = ∏_{q∈B}(1+1/(q−1))−1.
Indeed distinct moduli give at most one class for a head exponent vector and a block exponent vector; sum the geometric series in each fresh coordinate, omitting the all-zero exponents. This is a comparison of distributions, not a pointwise estimate on the original fibres.

Take a two-prime block and write a=1/(q−1), b=1/(r−1). Its A_B = a+b+ab ≤ [(2a+a²)+(2b+b²)]/2. Jensen for the fourth power gives
    P(blocked B) ≤ E(D⁴)[(2a+a²)^4+(2b+b²)^4]/2.
The same charge E(D⁴)(2a+a²)^4/2 suffices for a singleton prime because (2a)^4/2≥a^4. Thus all blocks with primes above 239 can be paid for by a single sum over the primes, independent of their pairing. For primes at most 239, which are necessarily singleton blocks under the forbidden assumptions, pay the existing 1-prime convex-tail bound.

The fourth moment follows from the tail-sum identity
    E[(1+T)^m] = 1 + sum_{e≥1} ((1+e)^m-e^m)/(s' p^(e−1)).
Expand the polynomial and sum geometric moments; take the product over six independent coordinates. The checker also verifies the m=2 crosscheck with the original expression. Above sieve cutoff 300,000, dominate the charge using (2+1/300000)^4 times the integral bound on the sum of (q−1)^−4, times 1/2.

Exact aggregate of all fresh blocked probabilities is at most 0.322270769143343303, rounded upward, below the old-only survivor lower bound. Choose an old survivor missing all blocked sets, then an uncovered tuple in each disjoint fresh block. CRT combines these into one integer. This proves the exclusion.

## General bounded blocks

For blocks of size at most k whose mixed primes are above cutoff K, the same argument uses
    A_B^m ≤ k^(m−1)(1+1/K)^(m(k−1)) ∑_{q∈B}(q−1)^−m.
For example exact checks pass at (k, K, m) = (3,401,4), (4,503,4), (8,1009,4), (16,2000,4).
A uniform but looser elementary consequence holds for every k≥1 at cutoff 20000k (second moment). Even paying the original full singleton budget as well, the extra big-block cost is at most E(D²)*10000/(9999*19999). This is obtained from the geometric-series bound on (1+1/(20000k))^(2k−2) and the all-integer squared reciprocal tail, and remains strictly within the original head-survivor margin.

Replay standalone independent extension calculation using the attached source and the two authenticated inputs from Mabel checkpoint 3: harrington_obstruction.py and harrington_seed.py. Scope is restricted; do not treat this as an unconditional obstruction to any odd covering.
