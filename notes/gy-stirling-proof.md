# A recurrence proof of Gy's second-kind Stirling inequality



**Scope and verification.** This is an alternative proof of a result already proved by René Gy. The full weak inequality and boundary equalities were reported Lean-verified in November 2026; the stricter interior characterization is a paper argument and has not independently been certified in Lean.



For every triple of natural numbers with 1 ≤ j ≤ p ≤ n, the product on the left below is at least the product on the right. Lean verified the second-kind assertion, including all endpoints, against mathlib’s `Nat.stirlingSecond`.

$$
S(p-1,j-1)S(n-1,p-1)S(n,j)\;\ge\;S(p,j)S(n,p)S(n-1,j-1).
$$

René Gy had already proved this inequality by a bijection. The proof here uses an induction on the two gaps between indices. It also gives a paper proof that equality holds precisely when j = 1, p = j, or p = n. The verified Lean declarations cover the weak inequality and the three boundary equalities.

# Fix the two gaps

For nonnegative integers b, r and d, set

$$
H_d(k)=S(k+d,k),\qquad F_{b,r}(k)=H_b(k+r)\,H_r(k),\qquad Q_{b,r}(k)=\frac{F_{b,r}(k)}{H_{b+r}(k)}.
$$

Use Q only for k ≥ 1. In that range H is positive: take k − 1 singleton blocks and put the remaining d + 1 elements into the last block. This also proves F and Q positive. If b = 0 or r = 0, the ratio is identically one since S(k,k) = 1.

We show that Q decreases with k. Write Δf(k) = f(k) − f(k − 1) for k ≥ 1. The Stirling recurrence gives ΔH_d(k) = k H_{d−1}(k) for d ≥ 1. For b,r ≥ 1 the product rule for finite differences gives

$$
\Delta F_{b,r}(k)=(k+r)F_{b-1,r}(k)+kF_{b,r-1}(k).
$$

To see the shift in the second term, take the difference of the first factor H_b(k + r) while holding the second at H_r(k). Then take the difference of the second factor while holding the first at H_b(k + r − 1). Put d = b + r. Since ΔH_d(k) is positive, division gives

$$
\frac{\Delta F_{b,r}(k)}{\Delta H_d(k)}=\left(1+\frac r k\right)Q_{b-1,r}(k)+Q_{b,r-1}(k).
$$

By induction on d, both smaller-gap ratios on the right weakly decrease. The first is positive and its factor 1 + r/k strictly decreases. Therefore the ratio of increments strictly decreases when both gaps are positive.

# From increments to the theorem

For b,r ≥ 1, both F and H start at zero. Their ratio at k is the weighted average of the first k increment ratios, with positive weights ΔH_d(i). Each new term lies below the previous average, so these averages strictly decrease. This proves the induction step. The Lean proof uses the cross-multiplied prefix-sum lemma `GySecond.prefix_ratio_rec`, which also handles zero increments.

For j ≥ 2 specialize to b = n − p and r = p − j. The two columns expand as follows.

| Column | F | H |
|---|---|---|
| j − 1 | S(n−1,p−1) S(p−1,j−1) | S(n−1,j−1) |
| j | S(n,p) S(p,j) | S(n,j) |

Cross multiplication of Q(j − 1) ≥ Q(j) yields the statement. If 1 < j < p < n, both gaps are positive and the inequality is strict. If p = j or p = n, the sides are equal by S(t,t) = 1. For j = 1 and p > 1, S(p−1,0) and S(n−1,0) both vanish. The case j = p = 1 was already included in p = j.

# Verification and experiments

`GySecond.gy_second_kind` was built with Lean 4.34.1 (compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`) and mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`. The clean `lake build` reported 903 jobs. A separate `lake env lean Audit.lean` printed the theorem and its axioms. Both completed successfully. The optional additional replay of compiled declarations was interrupted after these commands had finished.

```
'GySecond.gy_second_kind' depends on axioms: [propext, Quot.sound]
```

These are propositional extensionality and quotient soundness. Every project helper is proved. The certificate uses the Lean kernel and pinned dependencies. The Python computations and the prior preprint supply no axioms to the theorem.

An exact-integer recurrence checked all 171,700 triples with 1 ≤ j ≤ p ≤ n ≤ 100. There were 14,851 equalities on the stated boundaries, 156,849 strict inequalities, and zero counterexamples. In a separate exploratory test, an adjacent-row ratio inequality held strictly for all 4,753 tested pairs with 2 ≤ k < n ≤ 99. The universal proof uses the fixed-gap ratio above. The optional Lean strengthening to strictness did not complete verification before the compute host disconnected.

# Sources and attribution

1. René Gy, [On Certain Products of Three Stirling Numbers](https://math.colgate.edu/~integers/aa108/aa108.pdf), *Integers* 26 (2026), A108, Conjecture 2.1, printed p. 4. Published 24 August. Theorem 2.1 gives a binomial bound. The subsequent conjecture asks whether the bound tightens under a simultaneous index shift. The second-kind line uses braces and the ≥ direction.

2. René Gy, [Bijective Proofs of Inequalities Between Triple Products of Stirling Numbers](https://zenodo.org/records/22960306), 25 September 2026, DOI 10.5281/zenodo.22960306. Corollary 1.1, p. 3, gives the requested inequality verbatim. Pages 5–6 give the relevant bijection on colored words. Gy’s preprint also addresses the first kind.

3. Gy’s [2023 statement](https://math.stackexchange.com/questions/4652848/inequality-for-triple-product-of-stirling-numbers) and [2026 MathOverflow announcement](https://mathoverflow.net/questions/443153/inequality-for-symmetric-polynomial-functions-of-log-concave-variables/515544) trace the question to the preprint.

4. [Mathlib Stirling numbers](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Enumerative/Stirling.html) documents the definition. The [pinned source](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Combinatorics/Enumerative/Stirling.lean) specifies the version used.

The search on 18 November 2026 covered the original title, DOI, author, triple-product and symmetric-function formulations, arXiv literature search, and follow-up searches for an induction or Lean proof. The author’s MathOverflow answer led to the full preprint. This establishes Gy’s priority for the inequality. Priority for this recurrence argument or for formalizing the result remains undetermined.

