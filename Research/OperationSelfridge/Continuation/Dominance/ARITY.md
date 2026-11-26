# An unlimited-rank obstruction for low-arity prefix covers

**Theorem.** Consider the prefix atom model with heights 2, 1 and 1 at 3, 5 and 7, respectively. Adjoin any finite number of distinct odd primes at least 11, each at height zero. Each mode vector may be used at most once, with an arbitrary legal phase on every selected coordinate. There is no restriction on the available supports. A covering of the atom product requires at least **24 patterns fixing four or more coordinates**. When the normalized ternary unaries have the third-branch profile, at least **104** such patterns are necessary.

The second bound assumes the third-branch unary layout, or a lossless normalization of the given cover to that layout. For an arbitrary unnormalized cover, choose any lossless normalization. The number of its higher-arity labels is unchanged, so the weaker bound 24 always applies. This theorem applies beyond the released 3,303-slot catalogue, which itself has 1,169 high-arity labels. The theorem concerns the specified prefix heights. It imposes no unrestricted arity bound on integer covering systems.

| Normalized ternary unaries | Outward upper charge for all pair/triple labels | Additional labels of arity at least four permitted | Outward upper charge with all additions |
|---|---:|---:|---:|
| Third branch | 0.855327662983 | 103 | 0.999929936756 |
| Sibling | 0.931288993561 | 23 | 0.999354715642 |

## The surviving product and the scalar comparison

Insert missing unary labels, normalize them by the [coverage-preserving argument](README.md), then restrict to the product of the uncovered atoms on the individual axes. The uniform reference probability on each surviving alphabet gives the following bounds $u_{p,e}$ for the mass of any one phase at mode $e$. The ternary alphabet has nine surviving atoms, the quinary fifteen, and the septenary thirty-five.

| Coordinate | First mode | Second mode | Third mode |
|---|---:|---:|---:|
| 3, third branch | 5/9 | 2/9 | 1/9 |
| 3, sibling | 6/9 | 2/9 | 1/9 |
| 5 | 4/15 | 1/15 | |
| 7 | 6/35 | 1/35 | |
| $p\ge11$ | $1/(p-2)$ | | |

Use the distortion update at every prime in increasing order. Write $d_p=\delta_p$, $c_p=(1-d_p)^{-1}$ and $g_p(a)=c_p(a-d_p)_+$. Set $100d_p$ to $0,0,20,30,35,40,40,46$ at $3,5,7,11,13,17,19,23$, to 49 at the remaining primes below 101, and to 50 from 101 onwards. If the sum of upper bounds for the distorted masses of the stages is less than one, some atom word survives. The filter and the convex comparison are due to BBMST and Dai–Li–Li–Yi. [Dai–Li–Li–Yi, §2](https://arxiv.org/html/2611.15110v1)

For completeness, the scalar comparison on this finite product requires only the displayed phase-mass caps. A coordinate after distortion has conditional phase probabilities bounded by $c_pu_{p,e}$, even after all later stages, because the update preserves the earlier marginal. Introduce independent integer levels $T_p$ with $\Pr(T_p\ge e)=c_pu_{p,e}$. These probabilities decrease with $e$ and are at most one. In bounding the expectation of a convex increasing function of a sum of nonnegative weighted pattern indicators, replace each phase match in coordinate $p$ by $\mathbf 1_{T_p\ge e}$. To see the one-axis comparison, order the match indicators by decreasing upper probability. Telescope the convex function from their common base in that order. When an indicator fires, its increment is at most the increment if all preceding indicators in the list had fired, since the function is convex and the weights are nonnegative. Average and use its probability cap. The resulting sum of increments is exactly the expectation under the nested threshold events. Process coordinates backwards under conditioning, with independent later thresholds averaged. At the current stage, the covered fibre fraction is at most the sum of the allowed current-mode caps for all earlier-compatible slots. Apply the comparison to the convex positive-part function in $g_p$. Phase alignments need not actually attain this bound.

It suffices to include every eligible prime below the largest prime under consideration. Missing axes can be adjoined freely with their single unary and every possible pair/triple label. Any original covering still covers the enlarged product. The later comparisons then give an upper bound uniform in the largest prime.

## Counting all possible pairs and triples

At a current coordinate $p$, write $M_i=T_i$ for the earlier comparison levels. There are $\sum_i M_i$ eligible modes for a one-coordinate predecessor and $\sum_{i<j}M_iM_j$ eligible predecessor pairs. Thus the scalar load is the sum of these two counts times $\sum_e u_{p,e}$. For $p\ge11$, condition on the three head levels, set $k=T_3+T_5+T_7$ and $l=T_3T_5+T_3T_7+T_5T_7$, and let $S$ count successful preceding height-zero coordinates. The load is $n(S)/(p-2)$, where

$$
n(z)=k+l+(1+k)z+z(z-1)/2.
$$

The tail Bernoulli parameter at $q$ is $\beta_q=c_q/(q-2)$. The integer recurrence in the verifier aggregates the 36 exact head states by $(k,l)$. Up to $B=128^2$, it keeps $0\le z<160$. It rounds each probability upward in units of $10^{-20}$, using $P_{\rm new}(z)=(1-\beta)P(z)+\beta P(z-1)$. Its entries are nonnegative, so rounding is monotone and discarded high indices have no influence on retained indices. Each computed stage charge is rounded upward in the same units.

## The two tail bounds

We have $k\le7$, $l\le16$, and $2n(z)\le z^2+15z+46\le(z+8)^2-2$. For every $p\ge11$,

$$
\mathbb E\,2^S=\prod_{11\le q<p}(1+\beta_q)
 \le\prod_{m=11}^{p-1}\frac m{m-2}
 =\frac{(p-1)(p-2)}{90}.
$$

The left product is over the relevant primes. The integer upper product includes all intermediate integers. Also $(z+8)^2\le64\,2^{z/2}$ for all $z\ge0$, since each successive polynomial ratio is at most $(9/8)^2<\sqrt2$.

Since $g_p(n(z)/(p-2))\le (z+8)^2/(p-2)$, the omitted $S\ge160$ part for $p<B$ contributes in total at most $64B^2/(90\,2^{80})<10^{-15}$. Indeed on $S\ge160$ we have $2^{S/2}\le2^S2^{-80}$. For $p\ge B$, a positive part requires $2n(S)>p-2$, hence $S+8>\sqrt p$. The same comparison gives at most $(1024/90)(p-1)2^{-\sqrt p/2}$ per prime. Bound its sum over all integers $p\ge128^2$. For each $m\ge64$, the two square intervals with lower roots $2m$ and $2m+1$ together have $8m+4$ integers, every integer below $(2m+2)^2$. The exponential factor is at most $2^{-m}$. The ratio of successive majorants is

$$
\frac12\,\frac{8m+12}{8m+4}\left(\frac{2m+4}{2m+2}\right)^2<\frac34.
$$

Both rational factors decrease with $m$, so checking $m=64$ suffices. Four times the first block bounds this entire tail by less than $10^{-9}$. These two rational bounds are included in the reported charges.

## Pricing arbitrary high-arity labels

For a new mode vector $A$ of any arity, $\bigl(x+y-d\bigr)_+-(x-d)_+\le y$ for $y\ge0$. Its incremental scalar charge is therefore bounded by

$$
w(A)=\prod_{(p,e)\in A} c_pu_{p,e}.
$$

At its final prime this uses the slope $c_p$. At each earlier one it uses the independent comparison threshold probability. The same caps apply after adding other labels. Consequently the sum of the $K$ largest distinct-label weights bounds every set of at most $K$ additions.

The verifier retains the top 600 products among processed primes, separately for cardinalities $0,1,2,3,\ge4$. At each new prime it either omits the coordinate or multiplies by one of its mode weights. A discarded prefix in a category cannot reenter a top-600 list after multiplication by any fixed positive new factor. Equal weights of distinct labels are retained with multiplicity. Beyond 1,000 the new coordinate contributes at most $2/998$. The other factors of any label of arity at least four have product at most the best three-coordinate weight. Every factor is below one, and the three largest available single-coordinate maxima occur at $3,5,7$. The checker verifies that this tail bound is already below the 600th retained weight. Taking the largest 103 or 23 weights gives the displayed strict margins.

This is a written finite-product application of the published scalar comparison with exact rational rounding and analytic tails. No part of this new arity calculation was checked in Lean. The auxiliary-prime integer lift and its distinctness argument remain those of the previous prefix checkpoint. [Standard-library verifier](arity_tail.py) · [Exact output](arity_results.txt)
