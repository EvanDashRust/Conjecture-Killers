# In the first no-7 orbit, 37, 41, 43 and 47 all divide the period

Let a finite distinct odd covering have period $Q$, let $7\nmid Q$, and normalize the classes $3,5,9,15$ as in the [companion proof](README.md). If $r=1$, then each of $37,41,43,47$ divides $Q$. Thus every odd prime from 11 through 47 must divide $Q$ in this orbit. All powers of all actual primes remain unrestricted.

## Simultaneous reduction of the scalar estimate

Retain the product-conditioned smooth laws, their root-mass parameter $z$ and the mixed-head bound $C(z)$ from the companion proof. Assume one prime $b\in\{37,41,43,47\}$ is missing. Represent the admissible rough stages by primes $p\ge11$, omitting $b$. At each such prime let $t_p=\delta_p(p-1)$ and $c_p=(1-\delta_p)^{-1}$. After smoothing the congruence indicators, the state $d$ is the number of divisors of the random preceding product (with initial value $(1+T_3)(1+T_5)$). Filling every available label gives the stage-weight majorant $x=d/(p-1)$. For an actual family one may pad its finite period with additional rough coordinates and empty stages. Saturating the admissible divisor weights and then extending exponents upwards gives the comparison majorant by monotonicity of the published joint operator. This order allows an actual prime support with arbitrary gaps.

Write $g_p(x)=c_p(x-\delta_p)_+$ and $\kappa_p(x)=1/(1-x)$ for $x<\delta_p$, with $\kappa_p(x)=c_p$ otherwise. A comparison exponent $a$ at $p$ changes state $d$ to $(1+a)d$. This follows since each positive exponent contributes a fresh copy of every divisor already counted. The sharper distortion estimate of Dai–Li–Li–Yi, Lemmas 3.1–3.3 and (31)–(36), applies to these complete columns. We use $\vartheta_p=1/c_p$. Their pointwise comparison in the initial coordinates uses nested marginal caps just as in our scalar proof, now applying their vector rearrangement argument since the future bound is increasing and directionally convex. The resulting upper bound on the aggregate rough contribution is at most the scalar estimate minus
$$
 \sum_{p\in J}\sum_d \nu_{<p}(d)\,[c_p-\kappa_p(d/(p-1))]
 \min\{B_p^0(d),\,1/c_p\}.
$$
Here $J$ is a finite initial range of permitted rough stages. The common subprobability kernel for the stages before $p$ starts with the law of $d$ at the head. From state $d$, its mass at exponent 0 is $1-c_p/p$, and at exponent $e\ge1$ it is $\kappa_p(d/(p-1))(p-1)p^{-e-1}$. Both expectation branches in (34) dominate this kernel pointwise. Formula (36) sums the reductions without subtracting a possible improvement twice.

## Lower bounds on each reduction

Let $V_{>p}(n)$ be the complete scalar comparison cost for stages after $p$, entering with state $n$. Summation by parts in the $p$-coordinate gives
$$
 B_p^0(d)=\sum_{e\ge1}p^{-e}
       [V_{>p}((e+1)d)-V_{>p}(ed)].
$$
For a later prime $q$, write $R=\prod_{p<s<q}(1+T_s)$ over permitted primes, using the independent scalar law $\Pr(T_s\ge j)=c_s/s^j$. This prime contributes
$$
 \frac{c_q}{q-1}\,\mathbb E\!\left[((e+1)dR-t_q)_+-(edR-t_q)_+\right]
$$
to the square bracket. The integrand is nonnegative and nondecreasing in $R$. Below its first breakpoint it vanishes, between the breakpoints its slope is $(e+1)d$, and above the second breakpoint its slope is $d$. We may omit every term with $e$ above a chosen cutoff or $q$ above a chosen horizon. In the retained terms we clip the factor $1+T_s$ at four. For the 37, 41 and 43 calculations we keep $e\le3$ and clip the accumulated product at 128. For 47 we keep $e\le4$ and clip the product at 1,024.

The checker propagates componentwise lower masses by truncating nonnegative products downwards at scale $10^{16}$. For each $d,e$ it evaluates the last display from cumulative masses and cumulative first moments of this same lower histogram. This is an exact sum of its three nonnegative pieces. It also rounds each term of the lower common kernel down. States beyond the maximum positive-savings threshold for all stages in $J$ never contribute again. These deliberate finite omissions affect only the quantity *subtracted*. The full scalar upper bound and its infinite tail are retained, as detailed in the companion note.

The unrounded certified comparison expression is affine in the initial law. In particular the elementary finite lower recurrence may be idealized without rounding for the two endpoint checks. All later kernels, the functions $B_p^0(d)$, and the head cost are fixed or affine in $z$. Each endpoint's scalar upper and savings lower therefore bound the true comparison on the full interval $5/9\le z\le2/3$ via linear interpolation.

| Omitted prime | Last joint prime | Last prime tested for a later marginal decrease | Upper total charge at $z=5/9$ | Upper total charge at $z=2/3$ |
|---:|---:|---:|---:|---:|
| 37 | 47 | 349 | 0.9654830 | 0.9933178 |
| 41 | 131 | 1201 | 0.9688079 | 0.9968257 |
| 43 | 211 | 3001 | 0.9705716 | 0.9986945 |
| 47 | 499 | 8009 | 0.9753833 | 0.9996985 |

All eight displayed decimal bounds have been rounded upwards. The exact fractions are in [the 37 certificate](joint_37.txt), [the 41 certificate](joint_41.txt), [the 43 certificate](joint_43.txt), and [the 47 certificate](joint_47.txt). The 47 case uses a second schedule with eight adjusted small-prime thresholds, fixed across both endpoints. Its scalar positive-part prefix runs through 500,000 at the high endpoint and 60,000 at the low endpoint. The prefix choice affects only numerical upper estimation of the same scalar comparison. Each upper bound is below one, excluding its contrary assumption. See [Dai–Li–Li–Yi](https://arxiv.org/html/2611.15110v1) for the joint comparison used here.

Run each case from this directory.

    python3 joint_savings.py 37
    python3 joint_savings.py 41
    python3 joint_savings.py 43
    python3 joint_savings.py 47

These arguments and their exact-integer checkers have not been formalized in Lean.
