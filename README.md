# Conjecture Killers

Formal mathematics, auditable Lean 4 proofs, reproducible experiments, and careful attribution.

## Case 003: The eventual 9–6–3 conjecture

**Status: proved in Lean.** Every length from 25 onward has a disjoint congruence cover with three consecutive positions assigned moduli 9, 6, and 3 in that order. Length 24 is impossible, so 25 is the least eventual threshold.

[Proof, certificates, and replay instructions](Results/DisjointCovers/NINE_SIX_THREE.md)

## Case 002: Myerson’s disjoint congruence covers

**Status: proved in Lean.** For every length at least 17, there is a disjoint congruence cover with distinct moduli all at least 3 and at least two points per class. From length 132 onward, all the moduli can be multiples of 3.

[Proof, certificates, and replay instructions](Results/DisjointCovers/)

## Case 001: René Gy's second-kind Stirling inequality

**Status: alternative proof of an already-proved result, not a new solution to an open conjecture.**

For Stirling numbers of the second kind $S(n,k)$, the target from René Gy's Conjecture 2.1 states that whenever $1\le j\le p\le n$,

$$
S(p-1,j-1)\,S(n-1,p-1)\,S(n,j)\;\ge\;S(p,j)\,S(n,p)\,S(n-1,j-1).
$$

René Gy previously established this inequality **bijectively** in September 2026. The material here gives an **alternative fixed-gap recurrence and monotonicity proof**, together with its Lean 4 formalization. We make no claim of priority over Gy, or that the formalization is the first of its kind.

### Inspect the evidence

- [The mathematical proof, equality cases, and attribution](notes/gy-stirling-proof.md)
- [Formalized theorem](GySecond/Result.lean) (`GySecond.gy_second_kind`)
- [Supporting Lean modules](GySecond/)
- [Recorded verifier transcript and axioms](VERIFICATION_RECORD.md)
- [Exact-integer regression experiment](experiments/exact.py)
- [Build launcher](verify.sh)

### Reproduce

Recorded successful run on **18 November 2026**: Lean **4.34.1**, mathlib revision **`d13f23b723b8a846827a245b89c10fc7d3f11612`**. The original `lake build` finished 903 jobs, followed by an audit of the theorem. The reported axioms for the theorem were `[propext, Quot.sound]`. These are historical results; the GitHub publication is not a claim of an additional fresh Lean run.

With `elan`, `git`, Lake, and Python 3 installed:

```sh
bash verify.sh
python3 experiments/exact.py 100
```

The finite experiment independently checks 171,700 cases through `n = 100` and is not a substitute for a proof. **The weak inequality and boundary equalities** were formally checked; the strictness characterization is argued in the mathematical note but has **not** been Lean-verified.

### Sources

1. René Gy, [*On Certain Products of Three Stirling Numbers*](https://math.colgate.edu/~integers/aa108/aa108.pdf), *Integers* **26** (2026), A108, Conjecture 2.1.
2. René Gy, [*Bijective Proofs of Inequalities Between Triple Products of Stirling Numbers*](https://zenodo.org/records/22960306), September 25, 2026, Corollary 1.1; DOI [10.5281/zenodo.22960306](https://doi.org/10.5281/zenodo.22960306).
3. [Mathlib: Stirling numbers](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Enumerative/Stirling.html).

The work presented here was prepared for publication on November 18, 2026. **Conjecture Killers** is a project title; it does not imply that this particular conjecture was open when investigated.
