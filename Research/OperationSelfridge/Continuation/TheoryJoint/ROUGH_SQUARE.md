# A second digit at a prime beyond 5

Let a hypothetical covering have distinct odd numerical moduli greater than one, with least common multiple $Q$ not divisible by 7. Normalize $0\bmod3$, $0\bmod5$, $1\bmod15$, and $r\bmod9$ as in the [prior theorem](../Review/THIRD_PRIME.md). Define
$$
 S_1=\{11,13\},\qquad S_2=\{11,13,17,19,23\}.
$$

**Theorem.** There is a prime $p\in S_r$ with $p^2\mid Q$. More precisely, at least $p$ distinct numerical moduli are divisible by this same $p^2$. Their residue classes share a first digit at $p$ and between them use every possible second digit. This is a condition on arbitrary finite odd distinct covers in the no-7 branch, with no bound on the number or size of other primes or exponents. It does not assert that a specified prime is squared or that the numerical modulus $p^2$ itself occurs.

## Distortion estimate

Delete all classes whose moduli are divisible by $q^2$ for at least one $q\in S_r$, retaining the full original CRT period. The other classes will be called the residual family. Pure head classes and the four specified phases are untouched. We prove directly that the residual family misses a point; the original normalization and head estimates remain available even though the residual family need not cover.

A prime $p\in S_r$ has only exponent one among the potential moduli introduced at its stage. Thus summing fibre weights over $p$-exponents contributes $1/p$ instead of $1/(p-1)$. For subsequent stages the nested comparison needs only the event $T_p\ge1$. The divisor-count multiplier is $1+\mathrm{Bernoulli}(\gamma_p/p)$ with $\gamma_p=(1-\delta_p)^{-1}$. Its first and third moments are $1+\gamma_p/p$ and $1+7\gamma_p/p$. These conditional caps hold on the full period, since an actual cylinder depending only on its first digit has uniform mass $1/p$ before distortion, regardless of how many higher digits the ambient coordinate has. Primes outside $S_r$ use the unrestricted geometric comparison and its uncapped moments. The later tail uses the full prime indices as in the [quantile certificate](HEAD_QUANTILE.md).

For $r=2$ use that certificate's original 17-cell head, mass $s=45/68$, hinge law and unconditional third moment. At a capped stage use the adjusted denominator $p$ in both the hinge threshold and the scaling of its loss. With this change and the moment replacements above, the rigorous total $1-s+\mathrm{loss}$ is below $0.9999$.

For $r=1$ the [pure-coordinate endpoint comparison](../Alternative/README.md) gives a stronger restriction with a smaller set of capped primes. Its head survives all pure 3- and 5-classes by conditioning independently on their complements. The 3-root of larger mass has probability $z\in[5/9,2/3]$ and the remaining mixed head classes cost at most
$$
 C(z)=\tfrac43\big(\tfrac1{12}+(1-z)/5+z/20\big).
$$
For the number of available head divisors use $D=(1+T_3)(1+T_5)$ with that same $z$ for $\Pr(T_3\ge1)$, the caps $2/3^e$ for $e\ge2$, and $(4/3)/5^e$ for $e\ge1$. The unrounded prefix, middle and tail formulas and $C(z)$ are affine in $z$, since only the first two masses of the 3-exponent vary and all later kernels are fixed. The checker evaluates both endpoints separately with outward rounding. For $p=11,13$ it uses the one-digit rule, and all primes above 13 retain arbitrary powers. The endpoint charges are below $0.957019$ and $0.983735$, respectively. The capped probabilities used in the decreasing hinge correction are separate from the true first and third moments.

For both orbits the initial measures are different, but in each case a strict gap proves a surviving point of the residual family. The prefix ends at 180,000, the cubic sum at $10^7$, and the subsequent analytic prime bound uses $b=664578$. All prefix histograms, means and upper charges use scale $10^{20}$ and directed rounding. A missing prime can be padded in the upper comparison.

## A complete second-digit fibre

Fix the coordinates of a residual hole at every prime outside $S_r$ and fix its first digit at each prime in $S_r$ present in $Q$. Vary all higher digits at those primes. This whole product fibre escapes the residual classes because none of them reads the higher digits. If the original family covers, its deleted classes must cover every point of this fibre.

Ignore any deleted class disjoint from the fibre. Assign each remaining class to one $p\in S_r$ whose square divides its numerical modulus, for example the least eligible one. It specifies exactly one second digit at that prime, and its first digit must be the fixed one. If, at each eligible prime, its assigned classes omit some second digit, select one omitted digit per prime and extend arbitrarily to all higher digits. CRT gives a point of the product fibre avoiding every assigned class. Therefore some single eligible prime has assigned classes in all $p$ second-digit directions; at least $p$ distinct numerical moduli are necessary. Primes absent from the period or occurring to exponent one have no assigned classes.

## Replay

From the continuation directory run

    python3 TheoryJoint/orbit_quantile.py square2
    python3 TheoryJoint/orbit_quantile.py square1lo
    python3 TheoryJoint/orbit_quantile.py square1hi
    lake env lean TheoryJoint/HeadQuantile.lean

The integer and rational outputs are in [the verification record](QUANTILE_VERIFICATION.txt). The distortion theorem and the prime tail are from Dai, Li, Li and Yi. The head comparisons come from the cited project notes; their combination with these one-digit stages and the fibre consequence is a written, computationally assisted application. HeadQuantile.lean kernel checks the independent-choice step as full_digit_set, for arbitrary dependent products of digit sets. Its #print axioms reports propext, Classical.choice and Quot.sound. The distortion estimates, exact numerical recurrence, lifting from the period to the digit product and resulting universal statements remain outside Lean. The primary preprint and targeted literature search did not establish prior publication of the specific cutoff statements. [Dai et al.](https://arxiv.org/html/2611.15110v1)
