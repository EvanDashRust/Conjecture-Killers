# Restrictions on the third prime in an odd covering

Let $\mathcal D$ be a finite covering by distinct odd moduli greater than one, $Q=\operatorname{lcm}(\mathcal D)$, and $N_p$ the number of its moduli divisible by $p$.

- At least one of 7 and 11 divides $Q$. At least nine numerical moduli in total are divisible by 7 or 11.
- If $7\nmid Q$, all four primes $11,13,17,19$ divide $Q$, and $N_{11}\ge29$.
- If $7\nmid Q$, each of $3,5,9,15$ is an actual numerical modulus.
- If $7\nmid Q$, at least 50 moduli are divisible by 15. At least 36 of these have a further prime divisor of at least 11.
- If $11\nmid Q$, then $N_7\ge10$.

For example, in the absence of 7 the prime support already includes $3,5,11,13,17,19$. The distinction between divisibility of $Q$ and occurrence of a specific numerical modulus matters for the four small classes.

## A common comparison

Use the full period and the distortion construction and scalar comparison in [Dai, Li, Li and Yi](https://arxiv.org/abs/2611.15110), in the notation of the accompanying joint-fibre proof. Independently condition the 3- and 5-coordinates on avoiding all classes with pure-power moduli. Their caps are $g_3/3^e$ and $g_5/5^f$, with $g_3=2$ and $g_5=4/3$. On this product the union of all mixed head classes of moduli $3^a5^b$, $a,b\ge1$, has mass at most
$$
g_3g_5\sum_{a,b\ge1}3^{-a}5^{-b}=g_3g_5/8.
$$
Subsequent stages preserve the full head marginal, so this cost can be charged exactly once. If specified pure powers are absent, we replace the relevant cap by the stronger cap from the resulting geometric tail.

All moduli with at least one other prime are assigned to their largest prime $p$. For independent comparison exponents with $\Pr(T_q\ge e)=\gamma_q/q^e$, the number of possible head divisors is at most $(1+T_3)(1+T_5)$. Thus in the positive-part distortion bound the input to stage $p$ is
$$
D_p=(1+T_3)(1+T_5)\prod_{q<p,\ q\text{ in the tail}}(1+T_q).
$$
Distinctness bounds each available divisor at each $p$-exponent by one class. Prime coordinates explicitly omitted from the residual family need not be processed. Once past $10^7$ use the genuine full prime index $b=664578$ in Lemma 2.10. The omission of small primes changes the entering moment, and leaves the indices of the primes in the infinite tail unchanged.

The exact checker initializes the product histogram and true first- and third-moment upper bounds, then uses the upward-rounded positive-part and cubic estimates explained in JOINT_FIBRES.md. Its parameters are rational and within the range of the published distortion inequalities. If no modulus divisible by either 7 or 11 occurs, the numerical upper bound on the tail cost leaves mass greater than $0.181617$ after accounting for every head class. This excludes the proposed cover.

## Counts on the 7- and 11-coordinates

More generally delete all moduli divisible by 7 or 11, retaining the full period. The preceding construction supplies a measure under which the common set $H$ missed by the residual family has mass greater than $h=0.181617$ on the remaining coordinates. For a deleted modulus $m=7^a11^bd$ with $\gcd(d,77)=1$, its projection on the remaining coordinates has mass at most $W(d)=d^{-1}\prod_{q\mid d}\gamma_q$. Fixing the complete 7- and 11-coordinates requires the compatible projected classes to cover $H$. Replacing each weight by $\min(h,W(d))$ still gives total at least $h$ on every fibre. Average the result over the uniform 7- and 11-coordinates. It follows that the sum of $\min(h,W(d))/(7^a11^b)$ over the deleted moduli is at least $h$.

Sorting these weights for $m\le100000$ certifies that eight available moduli fall short. The same calculation with the prime 7 absent excludes 28 moduli, and with 11 absent excludes nine. The cutoff is justified by the bound $W(d)^4\le16/(3d^3)$ from the prime caps, which gives the same upper bound with $m$ for the fourth power of the averaged weight. The checker verifies each cutoff against the last retained weight.

## If 7 does not divide the period

Assume $7\nmid Q$. Suppressing one more prime stage at a time leaves the following mass margins with the tuned parameter table in the checker. In particular each missing prime is impossible.

| Other omitted prime | Lower bound on missed mass |
|---|---:|
| 11 | 0.181617 |
| 13 | 0.119046 |
| 17 | 0.032890 |
| 19 | 0.006492 |

We can alternatively omit a particular numerical modulus while retaining all prime stages from 11 onwards. If 3 is omitted then $g_3=6/5$ suffices. If 9 is omitted then $g_3=18/11$ suffices. If 5 is omitted the remaining pure 5-powers occupy at most $1/20$, giving $g_5=20/19$. For modulus 15 absent there is a different improvement: subtract $g_3g_5/15$ from the mixed-head sum, since the class of that numerical modulus is absent. Each case gives positive surviving mass.

| Omitted numerical modulus | Lower bound on missed mass |
|---|---:|
| 3 | 0.258950 |
| 5 | 0.006233 |
| 9 | 0.019088 |
| 15 | 0.000226 |

This proves the four individual occurrence conditions. A redundant class among them could be deleted. In particular the class of modulus 9 is disjoint from the class of modulus 3, and the class of modulus 15 is disjoint from the classes of moduli 3 and 5. An invertible affine map on the total period now normalizes these four classes to
$$
0\bmod3,\quad 0\bmod5,\quad 1\bmod15,\quad r\bmod9,\qquad r\in\{1,2\}.
$$
To see this, translate the two prime classes to zero, and scale by a unit independently modulo 3 and 5 to send the nonzero residues of the 15-class to 1. Adjust the translation by a multiple of 3 in the 3-adic coordinate so that the 9-class is represented by 1 or 2 exactly. CRT extends these choices to an invertible affine map on the full period.

Finally, still omitting prime 7, delete all classes with $15\mid m$. The comparison now uses $1+T_3+T_5$ at the head, and pays no mixed-head cost. Direct summation gives missed mass greater than $0.535333$. Restoring classes therefore requires $\sum_{15\mid m}W(m)>0.535333$. The checker bounds the sum of the largest 49 possible weights strictly below this target. The entire subset supported on $\{3,5\}$ contributes at most $1/3$, leaving more than $0.535333-1/3$ to be covered by moduli with a further prime divisor. Even the 35 largest such weights fall short. A cutoff of 200,000 is justified by the same fourth-power bound.

## Scope and verification

    python3 third_prime.py
    python3 third_prime.py --mixed-count
    for m in 3 5 9 15; do python3 third_prime.py --missing-with-seven "$m"; done
    for p in 13 17 19; do python3 third_prime.py --second-missing-prime "$p"; done

Use third_prime.py and joint_fibres.py from the same directory. The finite computations use rational arithmetic and explicitly directed integer rounding. The complete conditional statements are written, computer-assisted arguments. They do not provide a Lean proof of the unrestricted Erdős problem. A targeted priority search of the public claim ledger, project literature and the Dai et al. preprint identified no matching statement in those sources. Priority remains provisional. [Claim ledger](https://erdosproblems.ai/wiki/problems/covering_systems/E0007/claims) · [Erdős Problems #7](https://www.erdosproblems.com/7)
