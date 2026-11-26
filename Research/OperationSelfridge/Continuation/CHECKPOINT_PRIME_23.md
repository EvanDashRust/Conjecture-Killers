# The prime 23, prime support, and the rank-24 repair

This checkpoint continues PR 3 from `2d85ec0dac4cc06255f3b9f98fbb617bfda2a8af`. Neither orbit of the no-7 branch has been eliminated. All candidate families tested have explicit escaping integers.

## Consequences for an arbitrary finite odd distinct cover

Write Q for the least common multiple of the numerical moduli, and N(p) for the number divisible by p. At least **20** numerical moduli are divisible by 7 or 11, counting their union once. The previous bound was nine. Deleting these labels leaves one common residual set. Its simultaneous restorations on the 7 by 11 grid obey stronger constraints than two separate sums of weights. [Proof and exact grouped calculation](IndependentReview/GROUP_COUNTS.md)

If 7 does not divide Q, all of **3, 5, 11, 13, 17, 19, 23** divide Q; 3, 5, 9, 15 occur as actual numerical moduli. Moreover 27 and 25 divide Q, and at least one of 81 and 125 divides Q. For the new prime 23 restriction the close case is the second affine orbit. Deleting 23 there gives a certified upper distortion charge below 0.997347 relative to the 17 surviving cells modulo 45. It uses a fixed fraction of actual smooth-head holes throughout and a rigorous bound on all remaining primes. [Orbit 2 and exact certificates](TheoryJoint/HEAD_QUANTILE.md) · [Orbit 1 and prime powers](Alternative/README.md)

| Necessary in the no-7 branch | Orbit with 1 mod 9 | Orbit with 2 mod 9 |
|---|---:|---:|
| Distinct prime divisors of Q | ≥225 | ≥74 |
| Numerical moduli divisible by 25 or 27 and also by a prime ≥11 | ≥206 | ≥63 |
| Distinct primes ≥11 dividing those high-power mixed moduli | ≥10 | ≥6 |

The support bounds permit arbitrary prime values and exponents. For the first orbit, assuming at most 224 primes gives a charge below 0.999938. For the second, at most 73 gives a charge below 0.999294. Compressing prime-coordinate trees reduces each finite rank to its smallest eligible primes. A second implementation independently summed the geometric tails. The two sharp infima of ordinary smooth-head density are unchanged. [Prime-support proof](PrimeSupport/README.md) · [High-power mixed counts](FibrePacking/README.md)

In the first orbit, **every prime from 11 through 43 divides Q**, and 81 divides Q. At least one of 25 and 27 occurs as an actual modulus. In both orbits the bounds for N(11), N(13), N(17), N(19), N(23) are **58, 45, 32, 32, 37** respectively. Earlier lower bounds for N(15) and for its mixed subfamily still apply. [Joint prime-stage savings](Alternative/JOINT_SAVINGS.md) · [Fibre counts and 23 restoration](IndependentReview/COMMON_HOLE.md)

In the second orbit, 29 missing forces ordinary smooth-head hole density strictly below 53/200, against an infimum of 1/4. The numerical moduli 25, 27, 45 must all occur in this case. The effective 25-class must use residue 2, 3, or 4 modulo 5. The full proof records further phase conditions. A proof excluding 29 still needs to deal with their surviving choices. [Phase certificate](TheoryJoint/HEAD_QUANTILE.md)

## Constructive state

The released rank-24 template uses prime 7. The two unary profiles for its prefix trees are separate from the two arithmetic no-7 affine orbits above. At the original heights and with the full phase catalogue, the normalized unary choices reduce to two tree profiles. Rephasing a covered unary and then each already hidden mixed slot preserves all previous atom coverage. This recovered all 3,562 old observations for both archived layouts. Twenty later proposals covered their current banks and all twenty failed exact separation. The richest resumed bank has 4,526 labelled words and 4,525 distinct integer representatives. The original archives remain byte-for-byte intact. [Dominance proof, exact generator checks and resume command](Dominance/README.md) · [Uncovered products and repair lower bounds](SliceLearning/README.md)

Seed the next constructive search with `Dominance/sibling.json.gz` for the complete cumulative bank. The direct product verifier tests whether the union of the current patterns covers every point of a stored family. Preserve original coordinates and arithmetic witnesses when changing heights. The repaired latest and scored layouts each need at least nine legal slot edits on the fixed alphabet, even if new shapes are admitted. Rephasing one more unary cannot finish either layout.

## Verification and scope

Run commands in the linked proofs from `Research/OperationSelfridge/Continuation`. All exclusion checkers use exact arithmetic or explicit outward rounding. Search scores and tentative schedules play no role in an exclusion once the exact certificate is fixed. The new Lean 4.36.0 checks are limited to the named generic inequalities and rational margins in [HeadQuantile.lean](TheoryJoint/HeadQuantile.lean) and [SharedHole.lean](IndependentReview/SharedHole.lean). Their axiom lists are in [the head transcript](TheoryJoint/QUANTILE_VERIFICATION.txt) and [the common-hole transcript](IndependentReview/axioms.txt). The unrestricted implications, the uses of distortion, the finite recursions, and the primality and arithmetic enumerations retain written or computational dependencies.

Dai, Li, Li and Yi prove 45 divides Q and give their distortion and directional-convexity comparisons. The no-7 orbit restrictions, selected head quantile, finite-rank applications, and witness archives here are project results. The support comparison is conditional on 7 missing. Earlier prime-rank bounds have different hypotheses. Priority is provisional. [Dai et al.](https://arxiv.org/html/2611.15110v1) · [Schroeder](https://michaelschroeder.ai/research/NinePrimeSupport/companion)
