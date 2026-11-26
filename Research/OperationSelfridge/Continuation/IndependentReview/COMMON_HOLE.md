# Restoring classes on one common residual hole

The subsequent [grouped certificate](GROUP_COUNTS.md) raises the 7-or-11 bound below to 20, the isolated 7 bound to 20 and the isolated 11 and 13 bounds to 58 and 45. The pair and singleton computations in this note give the 17-, 19-, 23-, 29- and 31-incidence bounds.

Let a finite set of residue classes with pairwise distinct odd numerical moduli greater than 1 cover all integers. Write Q for its period, N(p) for the number of moduli divisible by p, and N(7 or 11) for the size of their union. Then

* N(7 or 11) is at least **14**, for every such cover.
* When 7 does not divide Q, the simultaneous lower bounds for N(11), N(13), N(17), N(19), N(23) are **39, 31, 32, 32, 37**. In the normalized orbit r=1 we additionally have N(23)≥40, N(29)≥50 and N(31)≥53.
* When 11 does not divide Q, N(7) is at least **14**.
* An inclusion-minimal covering in which both 7 and 11 divide Q has at least **17** moduli divisible by either.

The first four no-7 counts and the 7-or-11 conclusions use the previously certified distortion measures in [THIRD_PRIME.md](../Review/THIRD_PRIME.md). The finite arithmetic for the new deductions uses only fractions and integers. Every bound allows arbitrary prime support and exponents.

## Restoring a single coordinate

Suppose a common set H missed by all retained classes has probability greater than h on the coordinates other than a deleted prime p. For p=7 or 11 delete both 7 and 11 coordinates to form H, with h=0.181617; restore p on a fibre where the other deleted prime has no active labels. For p=13,17,19 work in the no-7 branch and delete every multiple of p. The certified margins h are respectively 0.119046, 0.032890 and 0.006492. In each application retain the full exponents in the original period. The earlier comparison gives each class modulo d on the remaining coordinates a probability at most

$$W(d)=d^{-1}\prod_{q\mid d}\gamma_q.$$

Use the schedule EARLY for 7 and 11, and MISSING_FIFTEEN for the other cases, as in the earlier omitted-prime proofs. Let ν be the conditional probability measure on H. Then every projected class modulo d has ν-mass at most min(1,W(d)/h). Two projected classes have intersection either empty or a single congruence class modulo their lcm.

Write a restored label as p times b, with b=p^{a-1}d, p coprime to d. On the product of ν and the uniform p-coordinate, covering implies the sum of individual masses is at least 1. Multiply by p. The normalized contribution of this label is its projected ν-mass times d/b, so the sum of normalized contributions must be at least p. Each numerical b can be used only once.

### The prime 23 and the two orbit measures

For p=23 keep the full original period while suppressing that rough prime's stage. In the r=2 orbit, the [quantile certificate](../TheoryJoint/orbit_quantile.py) starts from a subprobability ν₀ dominated by the uniform law on the full-head lifts of the 17 surviving cells modulo 45. Thus ν₀ is dominated by 45/17 times Haar probability on the full finite 3,5-head. On every rough coordinate q the conditional cylinder caps given earlier coordinates, including the full head, are γ(q)/q^e. Iteration under the final submeasure (successive stages preserve preceding marginals) gives a class cap
$$\frac{45}{17}\frac{1}{d}\prod_{q\mid d,\ q\ge11}\gamma(q).$$
Its surviving submeasure has mass greater than 0.00265 by the exact certificate. Hence after conditioning on this residual set the class cap is strictly less than $W_*(d)/0.001$, where $W_*(d)=d^{-1}\prod_{q\mid d,\ q\ge11}\gamma_*(q)$ and γ* is the larger of the two orbit schedules' caps at q. This follows since $0.00265(17/45)>0.001$. This calculation uses the dominating law of the full head, so thinning can concentrate the conditional law on a few cells without invalidating the bound.

The [r=1 omitted-stage certificate](../Alternative/power_orbits.py) gives mass greater than 0.052 after deleting the multiples of 23. The joint pure caps are at most $2(4/3)=8/3$. Since $0.052/(8/3)>0.001$, the same conditional estimate with $W_*(d)$ holds in this orbit. The weights $W_*$ use no inflation at 3 or 5. Use $h=0.001$, $W=W_*$ in the singleton and pair arguments below for both orbits.

Separately, in r=1 use the full stronger margins 0.052, 0.015 and 0.007 for omitted primes 23,29,31 respectively, with the original pure caps $2,4/3$. For these three omitted stages the singleton-cofactor enumeration below gives $\max \tau(D)=6,8,9$ respectively. Thus $N(p)\ge 2p-\max\tau(D)=40,50,53$, even before pair constraints.

## Singleton p-roots

Let k be an upper bound on the number of labels and suppose k<2p. Each of the p roots modulo p must receive some restored label. At least 2p−k roots have exactly one. Each such label must have p-exponent one, as a single deeper class misses a digit in its p-root. Its cofactor class must contain all of H. Let D be the lcm of these singleton cofactors. They have compatible phases, since their common intersection contains H. Thus H itself lies in one class modulo D, W(D)≥h, and the divisor count τ(D)≥2p−k by numerical distinctness. Without singleton information take D=1.

For all d let

$$w(d)=\min(1,W(\operatorname{lcm}(d,D))/h),\qquad u(b)=(d/b)w(d).$$

Then u(b) bounds a label's normalized contribution, including labels that have exponent greater than one at p. In the 17, 19 and 23 cases, enumerate the possible D above. The other cases take D=1 directly.

## Pair constraint and exact count certificate

Take two distinct first-power labels pa,pb, coprime cofactors to p, with their respective projected masses x,y. Since their union has ν-mass at most one and their intersection has mass at most w(lcm(a,b)),

$$x+y\le 1+w(\operatorname{lcm}(a,b)).$$

This exploits the same H on all p-fibres, even when the phases at p differ. In these formulas a,b need not be coprime to each other.

At rate λ>0 the sum contributed by at most k labels is bounded by

$$k\lambda+\sum_b (u(b)-\lambda)_+.$$

For a chosen pair a,b of first-power labels with u(a),u(b)≥λ, subtract the following nonnegative discount:

$$\min\{u(a)-\lambda,\ u(b)-\lambda,\ u(a)+u(b)-1-w(\operatorname{lcm}(a,b))\}.$$

If both labels are used, the joint intersection bound gives this discount. If either is absent, its full positive part is available as a discount in the baseline. The checker uses disjoint pairs, so all listed discounts may be applied. For cases with no pair certificate it sums the k largest single-label bounds instead.

The finite cutoff follows from W(d)^4≤(16/3)d^{-3}. Indeed γ(q)^4≤q except at 3, with γ(3)^4=16. The same upper bound (before division by h^4) applies to (d/b)W(d) as a function of b. Also W(lcm(d,D))≤W(d), since γ(q)≤q. Thus for b≥100000 the normalized contribution is <1/20 in the cases p≤19. For p=23, $W_*^4(d)≤d^{-3}$, and the analogous tail cap at this cutoff is 1/5. The certificate checks that each chosen λ is at least the tail cap or allows k potential omitted contributions at the tail cap in the sort. The same fourth-power bound limits every possible D. All primes absent from the period may be included in an upper comparison for label ranking.

| p | Labels assumed at most | Candidate D values tested | Worst upper sum (rounded up) | Required |
|---|---:|---:|---:|---:|
| 7 | 13 | 1 | 6.9870 | 7 |
| 11 | 38 | 1 | 10.9282 | 11 |
| 13 | 30 | 1 | 12.9888 | 13 |
| 17 | 31 | 10 | 16.3119 | 17 |
| 19 | 31 | 15 | 18.4542 | 19 |
| 23 | 36 | 18 | 22.9225 | 23 |

For p=7 or 11 the numerical calculation requires restoring only labels divisible by p and coprime to the other deleted prime.

## The unconditional union

Let A count labels divisible by 7 but coprime to 11, B those divisible by 11 but coprime to 7, and C those divisible by both. If A<7 and B<11, take the roots modulo 7 untouched by the A labels, and the roots modulo 11 untouched by the B labels. For any fixed point of H, their product consists of at least (7−A)(11−B) root pairs. Each of the C mixed labels can reach only one pair. Hence

$$A+B+C\ge A+B+(7-A)(11-B)=17+(6-A)(10-B)\ge17.$$

Suppose A+B+C≤13 instead. If A≥7 then B+C≤6, so there is an 11-root untouched by all 11-divisible labels. On that fibre the A labels must restore every H-point at every 7-coordinate. The 7 certificate above requires A≥14. If B≥11 then A+C≤2 and an untouched 7-root requires B≥39. This exhausts the possibilities and proves the unconditional bound.

In an inclusion-minimal cover every root at p must be touched by some p-divisible label whenever p divides the period; otherwise deleting all such labels still covers every integer by varying that coordinate into the untouched root. Thus when both primes divide the period, A≥7 implies B+C≥11, and B≥11 implies A+C≥7. In those two cases the union has at least 18 labels. The preceding grid inequality handles the remaining case, proving the stated bound of 17.

## Reproduction and attribution

From the continuation directory run `python3 IndependentReview/common_hole.py`. Exact outputs are in [counts.txt](counts.txt). The imported schedules, distortion lemma, full-period bounds and analytic tails are supplied by the previous checkpoint's written proof and its earlier rational certificates, including [the no-7 or no-11 calculation](../Review/results/third_prime.txt). Python checks only the subsequent enumerations and numerical contradictions in this file.

[SharedHole.lean](SharedHole.lean) in Lean 4.36.0 at mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842 checks the finite grid arithmetic, the singleton counting inequality, the both-present pair algebra, a set-theoretic replacement and a one-forbidden-phase lemma. Run `lake env lean /absolute/path/to/IndependentReview/SharedHole.lean` from that mathlib checkout. [Axiom records](axioms.txt) name each theorem. The full restoration argument and finite enumeration have no end-to-end Lean proof.

Dai, Li, Li and Yi supply the underlying distortion and coordinate caps. Their Theorem 1.1 states that 45 divides the period. This note builds on the project's omitted-stage margins by using one residual hole simultaneously in multiple root fibres. A targeted search in the primary preprint and public problem history identified no matching numerical result. Priority remains provisional. [Dai–Li–Li–Yi](https://arxiv.org/html/2611.15110v1) · [Erdős problem history](https://www.erdosproblems.com/history/7).
