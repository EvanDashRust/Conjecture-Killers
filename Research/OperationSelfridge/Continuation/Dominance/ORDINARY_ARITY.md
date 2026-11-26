# Four-prime numerical moduli when 7 is absent from the period

**Theorem.** Let a finite family of congruence classes with pairwise distinct odd moduli greater than one cover the integers, and let $Q$ be its least common multiple. If $7\nmid Q$, at least **1,712 distinct numerical moduli** have at least four distinct prime factors. Exponents, residues, the number of period primes and their sizes are arbitrary. At least **1,541** of them have largest prime factor at most $10^9$.

Michael Schroeder's September preprint already proves that every odd distinct covering needs a modulus with at least four distinct prime factors, including one with largest prime factor at most $10^9$. Its first theorem has an end-to-end Lean formalization. We use his complete cofactor count and scalar comparison for integer moduli. The no-7 count, the upper bound obtained by tracking 3 and 5 separately, and the restoration of the largest-weight exceptions are subsequent applications. Historical priority for the numerical counts has not been established. [Schroeder, primary paper and proof package](https://michaelschroeder.ai/research/ThreePrimeDivisors/companion) · [Unconditional quantitative corollaries of his bounds](SCHROEDER_RESTORATION.md)

## Reference measure and cofactor count

Work on the full CRT product of the actual period. At each $p\mid Q$, condition the uniform law of its entire prime-power coordinate on avoiding every pure $p$-power class. At most one class of each exponent occurs, so their total uniform mass is at most $\sum_{e\ge1}p^{-e}=1/(p-1)$. A class modulo $p^e$ has conditional mass at most $u_{p,e}=(p-1)p^{-e}/(p-2)$. Apply the usual normalized distortion at each increasing prime. Its upper multiplier is $c_p=1/(1-d_p)$ and its stage function $g_p(a)=c_p(a-d_p)_+$. Use $100d_p=0,0,35,40,44,46,46$ at $p=3,5,11,13,17,19,23$, respectively, and 50 at all other eligible primes. Use the product over all odd primes other than 7 in the comparison. Missing period factors and higher exponents than occur in the period enlarge this nonnegative comparison sum. The physical product and measure remain on the actual finite period.

First remove the putative exceptions, keeping the low-arity family with $\omega(m)\le3$, where $\omega$ counts distinct primes. Construct its distortion measure on the full period, with its actual pure classes. For each $p$, the final measure's conditional probability for a particular residue modulo $p^e$, given all earlier coordinates, is at most $c_p u_{p,e}$. Equivalently one may include the exceptions when constructing the measure and use the positive-part incremental bound. Using the measure adapted to the low-arity family suffices here.

Let independent $T_p$ have tails $\Pr(T_p\ge e)=c_pu_{p,e}$, for $e\ge1$. The conditional convex comparison applied at a mixed stage $p$ gives upper charge $\mathbb E\,g_p(N_p/(p-2))$, where

$$
N_p=\sum_{q<p}T_q+\sum_{q<r<p}T_qT_r .
$$

Indeed the earlier cofactor can have only one or two different prime factors. The present-coordinate caps sum to $1/(p-2)$ over all positive exponents. Distinctness provides at most one label for each complete exponent vector. This is Schroeder's Proposition 4.1, with prime 7 deleted from the comparison. The same threshold argument is detailed in the [finite-prefix calculation](ARITY.md). [Schroeder, §§2–4](https://michaelschroeder.ai/research/ThreePrimeDivisors/three_prime_factors_per_modulus.pdf)

There is no mixed stage contribution at 3. The stage at 5 costs at most $1/3$ since $\mathbb E T_3=1$ and $d_5=0$. At $p\ge11$, let $X=T_3$, $Y=T_5$, and $Z=\sum_{11\le q<p}T_q$. Keeping the first two previous primes distinct gives

$$
N_p\le X+Y+XY+(1+X+Y)Z+\binom Z2 .
$$

The last term allows pairs of distinct exponent marks from the same prime in $Z$. With $Y=y$, $Z=z$ the right side is $AX+B$ with $A=1+y+z$ and $B=y+(1+y)z+\binom z2$. In this paragraph $B$ is a cofactor intercept. Below we use $L$ for the prime cutoff.

## Integer recursion with unbounded exponents

Set $L=128^2$ and the rounding scale $D=10^{20}$. For $p<L$ carry $0\le z<160$ and $0\le y<48$. At each $p$ define $s=p-2$, $d=100d_p$ and $h=sd$. The positive part for the ternary variable starts at $k=\max(0,\lfloor(h-100B)/(100A)\rfloor+1)$. Its exact expected numerator is

$$
[100(Ak+B)-h]\Pr(X\ge k)+100A\,\mathbb E(X-k)_+.
$$

For $k\ge1$ these two statistics are $2/3^k$ and $1/3^k$. At $k=0$ they are both 1. The checker rounds each upward in units of $D^{-1}$ and uses the corresponding upper values at $k=80$ whenever $k>80$. All coefficients here are nonnegative. The quinary probabilities are $11/15$ at zero and $(16/15)5^{-y}$ for $y\ge1$.

The convolution updating the distribution of $Z$ adds one independent $T_p$. Its zero probability is $1-100(p-1)/[s(100-d)p]$, and its mass at $j\ge1$ is $100(p-1)^2/[s(100-d)p^2]\cdot p^{1-j}$. Compute the running geometrically weighted earlier probabilities by $H_z=P(z-1)+H_{z-1}/p$, starting with $H_0=0$. Round each intermediate contribution upward. After multiplying the three upward probability/expectation arrays for $X,Y,Z$ and dividing by $s(100-d)$, sum the scaled stage charges upward. This is the positive recurrence in the checker. Since the update adds nonnegative levels, discarded high $z$ cannot reenter the retained range.

Here are bounds for all material discarded by the two cutoffs and by the finite prime recursion. Let $S=X+Y+Z$. As in the prefix theorem, $g_p(N_p/(p-2))\le(S+8)^2/(p-2)\le64\,2^{S/2}/(p-2)$. For every $q\ge5$,

$$
\mathbb E 2^{T_q}=1+\frac{c_q(q-1)}{(q-2)^2}\le1+\frac2{q-3}=\frac{q-1}{q-3}.
$$

Also $\mathbb E2^{T_3}=3$. The product over $5\le q<p$ is bounded by the telescoping product over all integers from 5 to $p-1$. Thus $\mathbb E2^S\le(p-2)(p-3)/2$.

- For $Z\ge160$, also $S\ge160$, and $2^{S/2}\le2^S2^{-80}$. The total lost at primes $p<L$ is at most $32L^2/2^{80}$.
- For $Y\ge48$, independence gives $\mathbb E[2^S\mathbf 1_{Y\ge48}]\le\mathbb E2^S\cdot 2(2/5)^{48}$ since $\mathbb E[2^Y\mathbf 1_{Y\ge48}]=(16/9)(2/5)^{48}$ and $\mathbb E2^Y\ge1$. Over $p<L$ this costs at most $64L^2(2/5)^{48}$.
- At $p\ge L$, a positive part implies $2N_p>p-2$, hence $S+8>\sqrt p$. Use the same dyadic comparison to get at most $512(p-3)2^{-\sqrt p/2}$ per prime. The paired square-block bound in [the preceding proof](ARITY.md) gives the rational tail $512\cdot4(8m+4)(2m+2)^2/2^m$ at $m=64$.

All three corrections are included. The outward upper bound for the probability of the union of the low-arity classes is **0.547344095742**.

## Restoring the exceptions

The full-period measure above bounds the probability of a class with numerical modulus $m$ by $w(m)=\prod_{p^e\parallel m}c_pu_{p,e}$, by conditioning in decreasing order. Sum the heaviest $K$ distinct labels with $\omega(m)\ge4$ to bound any $K$ exceptions. The checker retains the 1,800 largest products for each of the support sizes $0,1,2,3,\ge4$ in a prime-by-prime dynamic program. Two different labels of equal weight remain separate. A discarded partial product can be paired with the same suffix as each of the 1,800 retained products in its category, so it cannot increase the value of any retained order statistic.

For this finite selection use primes below 2,800 and exponents at most 12. A missing prime contributes less than $2/2798$. Any excluded power contributes at most $8/3^{13}$, since all concentration constants here are below 8. The other three or more factors of an omitted high-arity modulus have product at most the largest three-coordinate product. The largest three eligible primes by individual phase weight are 3, 5 and 11; each larger-than-cutoff factor can be replaced by an unused one of those primes when bounding a triple. The verifier checks the excluded-label bound against the first order statistic beyond the allowed budget.

Restoring the **1,711** largest exception weights to the low-arity baseline gives total charge at most **0.999888601749**. This proves the 1,712 claim. These are counts of actual numerical moduli. The argument does not require that they all have different prime supports.

## Bounded largest prime

Use kernels adapted to the low-arity classes ending at primes at most $10^9$ and to all classes ending later. For the earlier stages the preceding low-arity sum remains an upper bound, and the conditional label caps remain valid. For the later stages Schroeder's unrestricted cofactor estimate bounds the stage probabilities by a sum involving $\mathbb E[\prod_{r<p}(1+T_r)^2]$. Each prime contributes the factor
$$
F_p(d)=1+\frac{(p-1)(3p-1)}{(p-2)(1-d)(p-1)^2}.
$$
Beyond $10^9$ our physical threshold agrees with his. At every earlier eligible prime our threshold is at most his except at 11. His comparison also includes 7. Thus our unrestricted far-tail sum is at most his certified $0.036711$ multiplied by
$$
F_{11}(35/100)\,[F_{11}(1/3) F_7(1/5)]^{-1}.
$$
This uses the prime-indexed second-moment comparison for each large ending prime, before his integral bound. Add this rational number to our baseline and repeat the same exception-weight selection. The ratio is $1810/3289$, so the extra far-tail cost is at most $6644691/328900000$. Adding the largest 1,540 exception weights still gives at most **0.999885775874**. At least 1,541 exceptions must have largest prime factor at most $10^9$, because the far stages already allowed arbitrary moduli. [Schroeder, §8, especially (8.1)–(8.7)](https://michaelschroeder.ai/research/ThreePrimeDivisors/three_prime_factors_per_modulus.pdf)

Reproduce all numbers with the standard Python interpreter on [ordinary_arity.py](ordinary_arity.py). The [exact results](ordinary_results.txt) give the cutoff ratio and both last strict margins. The new numerical restrictions use written proofs and exact integer arithmetic outside Lean.
