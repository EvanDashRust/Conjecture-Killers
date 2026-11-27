# High powers on the moduli involving large primes

Let a finite system of residue classes of pairwise distinct odd numerical moduli greater than one cover every integer, and suppose that 7 does not divide its period. Use the [established normalization](../Review/THIRD_PRIME.md) with classes 0 modulo 3, 0 modulo 5, 1 modulo 15, and $r$ modulo 9. Write $d=3^a5^b k$ where every prime factor of $k$ is at least 11. Call $k$ the rough part.

Among the moduli with $k>1$ the following counts are necessary. Each row counts a union once when both conditions hold.

| Exponents on that modulus | $r=1$ | $r=2$ |
|---|---:|---:|
| $a\ge3$ or $b\ge2$ | 206 | 63 |
| $a\ge3$ | 42 | 1 |
| $b\ge2$ | 53 | 1 |
| $a\ge4$ or $b\ge3$ | 22 | — |

The rough parts in the first row must collectively involve at least **ten distinct primes** when $r=1$, and at least **six** when $r=2$. Also, when $r=1$, **at least one of 25 and 27 occurs as an actual numerical modulus**. These are necessary conditions on arbitrary finite systems with the specified period and phases. These tests leave the existence question open in both orbits.

## Residual family and head measure

For each count row remove exactly its listed moduli with $k>1$, retaining the **full original period**. All smooth classes, including those with arbitrary powers of 3 and 5, remain. Condition the 3-coordinate and 5-coordinate independently on avoiding all their pure-power classes. A specified residue of positive exponent on these coordinates has mass at most $g_3/3^e$ and $g_5/5^e$, with $g_3=2$, $g_5=4/3$, by the geometric sums.

Write $A$ for the surviving 3-root containing the 9-class and $B$ for the other nonzero root. Before dividing by the pure-power survival probability, the mass available in $A$ is $2/9-x$ and in $B$ is $1/3-y$, where $x,y\ge0$ and $x+y\le 1/18$. These are union losses and allow redundancies and missing moduli. The conditional mass of $B$ is
$$t=\frac{1/3-y}{5/9-x-y}\in[5/9,2/3].$$
For fixed sum $x+y$ the extreme choices put the entire sum on one root, and the two resulting ratios move outwards as the sum increases. Since $t>1/2$, $t$ bounds the mass of every prescribed 3-root. The 15-class uses mass $w=1-t$ on its 3-root for $r=1$, and $w=t$ for $r=2$. Thus all mixed smooth classes together cost at most
$$ M(t)= w g_5/5 + t g_5/20 +(g_3/6)(g_5/4). $$
These terms treat $(a,b)=(1,1)$, $(1,b\ge2)$ and $(a\ge2,b\ge1)$ respectively. The distortion preserves this head marginal.

## Tail comparison and certification

Use the ascending-prime distortion of Dai–Li–Li–Yi on primes $p\ge11$, with the schedules in cross_heights.py. For each preceding rough prime $q$, take the independent comparison exponent satisfying $\Pr(T_q\ge e)=\gamma_q/q^e$, where $\gamma_q=(1-\delta_q)^{-1}$. Use $\Pr(T_3\ge1)=t$ and $\Pr(T_3\ge e)=g_3/3^e$ for $e\ge2$, and $\Pr(T_5\ge e)=g_5/5^e$. The first-coordinate modification follows directly from their one-coordinate nested-indicator comparison (Lemma 2.5 and the conditioning proof of Theorem 2.6). The marginal upper bounds for individual indicators suffice at that replacement step. There is no requirement for a geometric survival law.

Let $H_3,H_5$ be the upper exponents allowed for a **retained modulus with $k>1$**. Each numerical cofactor and new-prime exponent admit at most one class. The stage divisor-count comparator for the retained large-prime family is therefore
$$D_p=(1+\min(T_3,H_3))(1+\min(T_5,H_5))\prod_{11\le q<p}(1+T_q),$$
where $H=\infty$ is allowed and the product ranges over primes. Apply the published positive-part bound $\gamma_p\mathbb E(D_p-(p-1)\delta_p)_+/(p-1)$. All untruncated large-prime exponents are included. The resulting upper bound on the total covered mass, including $M(t)$, is affine in $t$ **before numerical rounding**, because changing $t$ only transfers probability between $T_3=0$ and 1. The middle and infinite cubic costs also depend linearly on the initial third moment. Upper bounds certified separately at both endpoints suffice.

The checker reuses [joint_fibres.py](../Review/joint_fibres.py) for integer upward rounding at scale $10^{20}$ through 60,000, the third-moment bound through $10^7$, and Dai et al. Lemma 2.10 with the full prime index $664578$. Larger primes absent from the actual period can be inserted in the upper comparison. For an unrestricted exponent the correction to $\mathbb E(1+T_3)^j$ is $(2^j-1)(t-g_3/3)$. Finite caps use summation of tail probabilities. Exact endpoint margins appear in cross_results.txt.

## Restoring the removed classes

On the full original period the final law obeys the iterated conditional caps. Each removed class has mass at most
$$ W(d)=d^{-1}\prod_{p\mid d}\gamma_p,\qquad \gamma_3=2,\quad\gamma_5=4/3.$$
Thus the sum of its family's distinct weights exceeds the lower margin in [high_counts.py](high_counts.py). The script enumerates all candidate moduli up to 400,000, checks the endpoint margins, and sums weights in decreasing order. Beyond that cutoff, $W(d)^4\le16/(3d^3)$ since $\gamma_p^4\le p$ for $p\ne3$ and $\gamma_3^4=16$. This bound is below the final retained cutoff weight in each row.

For the prime-support assertion, summing $W(3^a5^b)$ over every allowed smooth part with $a\ge3$ or $b\ge2$ gives exactly
$$ S=\frac{2}{18}\left(1+\frac{4/3}{4}\right)+\frac{4/3}{20}\left(1+\frac23+\frac29\right)=\frac{37}{135}. $$
If all the rough parts of these classes have prime support contained in $P$, summation over all their powers bounds total weight by $S(\prod_{p\in P}(1+\gamma_p/(p-1))-1)$. Even the nine largest Euler factors give only $33410297/145981440$ against the $r=1$ margin $0.24234$. The five largest give $7807/51840$ against the $r=2$ margin $0.15345$.

## The numerical 25 or 27 disjunction

If both 25 and 27 are absent, $x+y\le1/54$ and the pure 5-tower above 5 costs at most $1/100$. Thus $g_3=54/29$, $g_5=100/79$ suffice, and $17/29\le t\le18/29$. Keep the same mixed-head formula with $w=1-t$ and take both tail height caps infinite. At the two endpoints the total covered-mass upper bounds are $0.987860$ and $0.998595$ rounded upwards. This excludes joint absence for $r=1$. In particular either a 25-class lies outside the 5-class, or a 27-class lies outside the union of the 3- and 9-classes. Otherwise both labels could be deleted while preserving coverage.

## Reproduction and attribution

From this directory run

```bash
for mode in both high3 high5 next; do
  for t in 0 1; do python3 cross_heights.py "$mode" --endpoint "$t"; done
done
python3 high_counts.py
python3 high_support.py
python3 root_caps.py
```

The four archived transcripts retain exact fractions. The arguments are written proofs and rational computations. No new statement here is kernel checked. The distortion method, joint/nested comparison machinery and analytic prime-tail estimate are due to the cited authors and predecessors. A targeted search of the primary literature below found no matching local high-power counts or support claim. Priority remains provisional. [Dai–Li–Li–Yi](https://arxiv.org/html/2611.15110v1) · [Hough–Nielsen](https://www.math.stonybrook.edu/~rdhough/covering_restricted.pdf) · [Guo–Sun](https://arxiv.org/abs/math/0412217)

## Which small labels must survive if 29 is absent

This consequence uses the independent [head-quantile certificate](../TheoryJoint/HEAD_QUANTILE.md) for $r=2$, which requires ordinary smooth-head gap $G<53/200$ if 29 is absent from the period. For a pure-prime union of ordinary density $1/2-\alpha$ on the 3-coordinate and $1/4-\beta$ on the 5-coordinate, write $E$ for their union on the product. Let $L$ sum $1/m$ over every missing smooth mixed label $m$, and let $J$ be the excess of the sum of individual present mixed-class densities over their union density **outside** $E$. This gives the identity
$$G=\frac14+\frac34\alpha+\frac12\beta+\alpha\beta+L+J.$$
Indeed, the complement of the two pure unions has mass $(1/2+\alpha)(3/4+\beta)$ and the total possible mixed mass is $1/8$. Every correction shown is nonnegative. Omitting a pure label $3^a$ costs $\alpha\ge3^{-a}$ and similarly for 5.

Thus numerical 25, 27 and 45 all occur in this branch. Each omission by itself would imply a head gap of at least $27/100$, $5/18$, or $1/4+1/45$, respectively. Moreover the 25- and 27-classes cannot both have their low root equal to that of the 15-class on the corresponding prime. Otherwise its overlap with their union would contribute at least $1/75+1/135-1/675=13/675$ to $J$, exceeding $53/200-1/4=3/200$.

If **25 is assigned a residue equal to 1 modulo 5**, its overlap with 15 alone costs $1/75$. This leaves strictly less than $3/200-1/75=1/600$ for $3\alpha/4+\beta/2+L$. Every mixed smooth numerical label smaller than 600 must then occur, namely 15, 45, 75, 135, 225, 375 and 405. Every pure label among 3, 9, 27, 81, 243, 5, 25 and 125 must occur as well. If **27 is assigned a residue equal to 1 modulo 3**, its overlap with 15 costs $1/135$ and the residual allowance is $41/5400$. This forces the actual numerical labels 75 and 81 in addition to 25, 27 and 45. These are intra-orbit restrictions and depend on the head-gap certificate.

Numerical experimentation with the higher-digit caps conditioned on both 25 and 27 still yielded upper charges above 1 with 29 absent. The preceding deficit conclusions only use the proved head-gap bound.
