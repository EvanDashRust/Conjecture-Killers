# Prime powers and the phase of modulus 15 in the no-7 branch

Let a finite distinct covering have odd numerical moduli greater than one, period $Q$, and $7\nmid Q$. The existing normalization gives $0\bmod3,0\bmod5,1\bmod15,r\bmod9$. The following necessary conditions allow arbitrary further prime factors and exponents.

| Hypothesis | Divisibility required |
|---|---|
| Either orbit | $27\mid Q, 25\mid Q$, and $81\mid Q$ or $125\mid Q$ |
| $r=1$ | $81\mid Q, 23\cdot29\cdot31\mid Q$, and $243\mid Q$ or $125\mid Q$ |

These conditions concern the least common multiple. An individual period divisor need not occur as a numerical modulus. The results are written and computer-assisted.

## Head law and cofactor constraints

Use the full CRT period, with 3 and 5 first. Suppose $v_3(Q)\le A$ and $v_5(Q)\le B$. An unspecified bound means infinity. Put
$$
U=\sum_{e=1}^A3^{-e},\quad V=\sum_{f=1}^B5^{-f},\quad
g_3=(1-U)^{-1},\quad g_5=(1-V)^{-1}.
$$
Condition the uniform laws in the two coordinates independently on avoiding all pure-power classes. Numerical distinctness bounds their union masses by $U,V$ before conditioning. Specified positive-exponent cylinders have probabilities at most $g_3/3^e,g_5/5^f$. The sum of probabilities of all mixed head classes is at most $g_3g_5UV$. Use this head cost for the rows applicable to either orbit.

For $r=1$, the normalized 9-class sits in the same ternary root as the 15-class. Let $X,Y$ be the unconditioned masses removed by pure powers in roots 1 and 2 modulo 3. Then $X\ge1/9, Y\le U-4/9\le1/18$. In the conditioned 3-law, root 1 has mass $1-z$ and root 2 has mass
$$
z=\frac{1/3-Y}{2/3-X-Y},\qquad
(7/9-U)g_3\le z\le g_3/3.
$$
Indeed $z$ increases in $X$ and decreases in $Y$. In particular root 2 is the heavier root. The class $1\bmod15$ must use the lighter root. Bound the mixed classes with ternary exponent at least two by the usual caps. The mixed classes with ternary exponent one and quinary exponent at least two can use the heavier root. This gives the head loss upper bound
$$
C(z)=g_5\left[g_3(U-1/3)V+(1-z)/5+z(V-1/5)\right].
$$

For comparison at larger primes retain this *same* root mass. Take independent nonnegative integer exponents $T_3,T_5$ truncated at $A,B$ respectively (unbounded when the corresponding bound is infinity). Set their survival probabilities to $g_q/q^e$ for positive admissible $e$, with $\Pr(T_3\ge1)=z$ in the first orbit. In the orbit-independent comparison use $z=g_3/3$. These are decreasing sequences and upper bound every actual cylinder mass at its respective exponent. The proof of Dai–Li–Li–Yi Theorem 2.6 extends to these caps. Condition from the last coordinate backwards and apply their Lemma 2.5 in each coordinate. The events $T_q\ge e$ are nested, exactly as in that proof.

The comparator number of head exponents dividing the random smooth part is $D=(1+T_3)(1+T_5)$. At a larger prime $p$, write $Z_p=\prod_{11\le q<p}(1+T_q)$ over the permitted rough primes with $\Pr(T_q\ge e)=\gamma_q/q^e,\ \gamma_q=(1-\delta_q)^{-1}$. Omit any explicitly excluded prime in both the stages and this product. Distinctness allows at most one class per cofactor and positive $p$-exponent. The stage loss is at most
$$
\frac{\gamma_p}{p-1}\mathbb E\big(DZ_p-\delta_p(p-1)\big)_+ .
$$
Absent primes can be included to upper bound this scalar quantity. Previous marginals are preserved and the mixed head cost is charged once. At fixed valuation bounds and schedule, the distribution of $T_3$ is affine in $z$ because only its masses at zero and one vary. The exact sum of stage upper bounds plus $C(z)$ is affine in $z$, as is the unrounded capped-correction and third-moment majorant. Either expression can therefore be bounded by checking both endpoints before outward rounding.

## Certificates

| Contrary assumption | Minimum rigorous surviving mass over tested endpoints |
|---|---:|
| $v_3(Q)\le2$ | $>0.129139495$ |
| $v_5(Q)\le1$ | $>0.101081074$ |
| $v_3(Q)\le3, v_5(Q)\le2$ | $>0.006442410$ |
| $r=1, v_3(Q)\le3$ | $>0.020140928$ |
| $r=1, v_3(Q)\le4, v_5(Q)\le2$ | $>0.016081740$ |
| $r=1, 23\nmid Q$ | $>0.054512746$ |
| $r=1, 29\nmid Q$ | $>0.016535020$ |
| $r=1, 31\nmid Q$ | $>0.008114144$ |

Run `python3 power_orbits.py` from this directory. A case name and optional `--endpoint lo` or `--endpoint hi` replay one line. [Exact transcripts](certificates.txt) give each head, prefix, middle, and infinite-tail cost. The inherited rational schedule is `MISSING_FIFTEEN` in [third_prime.py](../Review/third_prime.py). The finite recurrence from [joint_fibres.py](../Review/joint_fibres.py) uses rounding upwards at scale $10^{20}$. Through 60,000 it caps comparison factors only in the decreasing positive-part correction while using the true first moment. Through $10^7$ it uses the uncapped cubic moment. The remaining infinite tail uses Dai–Li–Li–Yi Lemma 2.10 with genuine prime index 664578, retaining the recalculated incoming cubic moment.

These are applications of the published distortion, conditional rearrangement and tail bounds. The head accounting ties the *fixed residue of 15* to the same extremal root mass used in the tail. Making each estimate independently would miss the 29 and 31 exclusions. The linked preprint proves $45\mid Q$ and a least-modulus upper bound of 9, and the earlier project note supplies the no-7 normalization. The sources checked do not establish priority of the divisibility statements here. No new Lean proof is claimed in this directory. [Dai–Li–Li–Yi](https://arxiv.org/html/2611.15110v1) · [No-7 normalization](../Review/THIRD_PRIME.md) · [Prior-project ledger](https://the-omega-institute.github.io/trureturing-mdbook/Problems/erdos-7-odd-covering-systems.html)

## Independent check of the companion orbit-2 quantile

For the companion calculation with 23 omitted, we reviewed how the surviving head set enters the distortion inequality. With $s=45/68$, the uniform law on the 17 initially surviving cells and their higher-digit extensions gives the true smooth holes mass at least $s$. Thin those holes with a constant density if needed to obtain a weight $0\le f\le1$ of mass exactly $s$. For any measured nonnegative input $X$ and $v\ge t$,
$$
\mathbb E[f(X-t)_+] \le \mathbb E[(X-v)_+]+s(v-t).
$$
The distortion comparison for the rough coordinates can first hold the head fixed. After conditioning on the resulting rough exponents, the last display applies on the actual head. This order permits an arbitrary dependence of $f$ on the true smooth phases and upper digits.

On each fixed upper-exponent pair, subtract the maximal full-cell mean from the positive-part envelope and add the threshold. Its remaining lower-hinge correction is the maximum over complements of the threshold times the complement mass minus the loss in each shape's maximum intersection. All those losses are nonnegative. Capping high exponent multiplicities therefore increases the correction. The first moment outside that correction and the unconditional third moment in the analytic tail still use uncapped exponents. Choosing $v=\max(t,4/3)$ in the normalized head variable gives the retained-atom formula in the companion checker. We also checked that roundings of the cumulative atom masses and their cumulative offsets go in opposite directions as required by the subtraction in the lower hinge.

Run `python3 check_quantile.py` to compare a separate direct complement computation with the retained-atom evaluator at 14 thresholds, including points below, at and above the quantile. It checks all $2^{17}$ subsets and 100 capped exponent pairs. This finite comparison supplements the written proof and does not replace the companion unrestricted-tail certificate. [Independent replay](quantile_review.txt) · [Companion checker](../TheoryJoint/orbit_quantile.py)
