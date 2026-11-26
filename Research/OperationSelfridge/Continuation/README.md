# Operation Selfridge continuation

Erdős Problem 7 remains open. This pass gives lower bounds on the number of classes any hypothetical cover needs at primes 3 and 5, a stronger obstruction to extending Harrington's near-cover, and an equivalent finite search model with more freedom than the original valuation box.

## Results

- **Any hypothetical odd cover needs at least 18 moduli divisible by 3 and 11 divisible by 5.** If modulus 3 is absent, at least 39 moduli must be divisible by 3. The fibre bounds allow arbitrary prime support and exponents. [Proof and replay](FIBRE_COUNTS.md)
- **At least six mixed classes are needed to extend the Harrington seed.** The result permits any number of old-prime-only and single-fresh-prime additions and arbitrary exponents. More generally, any completion must have a nonempty set of at least two fresh primes on which all but at most one weighted incident load exceeds its threshold.
- **Fixed prefixes and variable exits give an equivalent finite-box formulation.** Modes can fix a low prime-power residue or identify the first nonzero digit beyond that prefix. A complete finite box in the model lifts to explicit odd congruences. Every odd covering has a representation in this model. The searched configurations still have exact holes.
- **Vivian's handoff reproduced.** Both Gmail checkers ran successfully. Her nine-coordinate bound and frozen ten-coordinate diagnostic agree with the archived data. I used the verified rank-20 hole to seed counterexample-guided searches and allowed existing phases to move.

## 1. Weighted mixed-prime obstruction

Fix the 2,471-class Harrington near-cover from checkpoint 3, including its specified residues. Write $P=\{3,5,7,11,13,17\}$. An added modulus is mixed if it has at least two distinct prime factors outside $P$. Write $T(m)$ for its set of prime factors outside $P$ and $\nu_q(m)$ for the exponent at $q$. For a set $U$ of fresh primes and $q\in U$, define the weighted load

$$
C_q(U)=\sum_{m\ \mathrm{mixed},\,q\in T(m)\subseteq U}q^{-\nu_q(m)},
\qquad b_q=\max(1/6,5/q).
$$

**Theorem.** If every subset $U$ of the fresh prime set with $|U|\ge2$ contains at least two primes $q$ with $C_q(U)\le b_q$, the enlarged system misses an integer. Any completion therefore has a set $U$ with at most one such prime. In particular, every completion uses at least six mixed moduli. This follows because $U$ then has at least one prime with $C_q(U)>b_q\ge5/q$, and each term has size at most $1/q$.

The assumption covers arbitrary interaction graphs when each prime's total incident load stays within $b_q$. It also covers forests of binary fresh-prime interactions when each edge separately has load at most $b_q$ at each of its endpoints. Multiple congruences can contribute to the same edge and the bound uses their summed weights. If precisely six mixed classes appear in a completion, at least one prime $q\le31$ must belong to all six, with exponent 1 in at least five of the six. Otherwise the required load above $b_q$ is impossible.

### Product law and quantitative certificate

Use the seed-free product domain and single-coordinate conditioning from checkpoint 3. The probability of surviving all old-prime-only additions is at least the Shearer polynomial of the full head, computed with the old numerical labels reserved. Its exact lower bound is greater than $0.32233258$.

For each fresh prime $q$, let $\alpha_q(x)$ be the fraction of its fibre covered by the additions that use $q$ as their only fresh prime. For $q\le40000$, choose a rational threshold $\theta_q=t/(q-1)$ with $0\le\theta_q\le1-2b_q$. Put
$$
g_q(z)=\frac{(z-\theta_q)_+}{1-\theta_q}.
$$
For $q>40000$ put $g_q(z)=z^2$. In each case $g_q(1)=1$, and if $z\ge1-b_q$ then $g_q(z)\ge1/2$. The linear statement follows by rearranging the bound on $\theta_q$. The quadratic statement uses $b_q=1/6$ for these primes and $(5/6)^2>1/2$.

The checkpoint 3 convex comparison bounds each expected payoff by the same payoff evaluated on $D/(q-1)$, with $D$ the product of six independent shifted geometric variables for the conditioned head. The integer checker computes outward bounds on the distribution of $D$ and on the positive-part payoff. For $q>40000$ it uses the second moment and an exact prime enumeration through 600,000. Beyond that, $q-1$ is even. The reciprocal-square sum is bounded by the first even term plus the integral on the remaining even denominators. The computation gives
$$
\sum_q\mathbb E g_q(\alpha_q)<0.32144136.
$$

The finite positive-part minimization can use binary search. If $r=q-1$, the sign of the adjacent difference for $N_t/(r-t)$, where $N_t=\mathbb E(D-t)_+$, is the sign of $\mathbb E[(D-r)1_{D>t}]$. This expression is nondecreasing for $t<r$. The outward-rounded numerator used by the checker has the same monotonicity, since the corresponding change at an integer threshold is an outward probability count times a nonnegative factor.

Since the expected aggregate payoff is strictly less than the guaranteed probability of surviving all old-only additions, there is an old-prime assignment $x$ avoiding the seed and all old-only additions with $G(x)=\sum_q g_q(\alpha_q(x))<1$. No fresh-prime fibre is completely covered. At most one fresh prime has surviving fibre mass at most $b_q$, because two such primes would contribute at least 1 to $G$.

### Assign and avoid the mixed classes

Peel the fresh prime set from full size downward. At each step with at least two primes, choose a prime in the current set $U$ with load at most $b_q$ whose surviving fibre mass exceeds $b_q$. Such a choice exists because there are at least two low-load primes and at most one exceptional prime. Assign to the removed prime all still-unassigned mixed classes that contain it. At that step an unassigned support is contained in $U$. Thus the sum of the assigned forbidden fibre fractions is at most $C_q(U)$. Each removed prime can choose a surviving residue outside the union of all forbidden prefixes assigned to it. No mixed class can be left at a singleton. The final prime has a surviving residue because its payoff is less than 1. CRT combines the chosen fresh residues with the old assignment into an uncovered integer.

The three-prime head and sparse-tail results in the Trureturing ledger use related block-saturation reasoning. The present result retains the specified six-prime seed and starts the fresh primes at 19. It uses a weighted condition on the actual congruence labels, including their prime-power exponents. Priority remains provisional. [Checkpoint 3](../README.md) · [Trureturing block-saturation report](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/06-block-saturation-and-the-actual-crossing-budget.md) · [Dai, Li, Li and Yi](https://arxiv.org/abs/2611.15110)

## 2. Prefix-box search equivalent to Erdős #7

Choose distinct odd core primes $p_i$ and nonnegative heights $h_i$. The finite alphabet at prime $p$ and height $h$ consists of pairs $(r,d)$ with $0\le r<p^h$ and $1\le d<p$. Every coordinate of a pattern is free or takes one of the following modes.

- Fixed depth $e$ for $1\le e\le h$. The pattern assigns the value of $r\bmod p^e$.
- Variable depth. The pattern assigns one complete pair $(r,d)$.

Require every pattern to use a nonempty mode vector and allow at most one phase assignment per mode vector. The resulting finite box has a cover for some choices of primes and heights if and only if an odd distinct covering exists.

**From an odd cover to the box.** Use all primes in its period and take $h_i$ equal to the largest corresponding exponent. A class of modulus $\prod_i p_i^{e_i}$ maps to fixed depth $e_i$ at each participating coordinate. Distinctness gives distinct vectors. For any atom word the Chinese remainder theorem supplies an integer with those low prefixes $r_i$. Some original class covers that integer, so its pattern contains the word.

**From the box to an odd cover.** For each prime $p$ and each root $r\bmod p^h$, choose a distinct odd auxiliary prime $q_{p,r}>h+1$ not among the core primes. Add the class $0\bmod q_{p,r}$ and, for $1\le j<q_{p,r}$, the CRT class requiring $x\equiv r\pmod{p^j}$ and $x\equiv j\pmod{q_{p,r}}$. At a variable-depth coordinate whose pattern assigns $(r,d)$, use one copy for each $h\le k\le q_{p,r}-2$, with residue $r+d p^k\bmod p^{k+1}$. Keep fixed-depth coordinates as given and combine the coordinate congruences by CRT.

An integer escaping all auxiliary classes has, at every core prime, a root $r=x\bmod p^h$ and a finite first exit $k=\nu_p(x-r)$ between $h$ and $q_{p,r}-2$. Its digit $d=(x-r)/p^k\bmod p$ is nonzero. These roots and digits give an atom word. A box pattern covering the word supplies an actual class containing the integer. Every constructed modulus determines its mode vector from the prime-factor exponents, with exponent zero for a free coordinate, exponents at most $h$ for fixed depth, and higher exponents for variable depth. Within one mode vector the exponent tuple determines the copy. The auxiliary primes distinguish their own classes from the box classes and from the other auxiliary families. All moduli are odd and greater than one.

The height-zero specialization recovers the original valuation-box method. The prefix-tree representation and auxiliary-prime technique draw on the covering-system literature and checkpoint 2. The explicit generator has an even positive control checked over its full period and a negative control with a removed pattern. The full bidirectional argument is written above. Lean checks the integer first-exit lemma used in the lift. [Harrington, Sun and Wong](https://doi.org/10.1016/j.disc.2022.112936) · [Bispels et al.](https://doi.org/10.1016/j.disc.2026.115013)

## 3. Experimental record

- The first unconstrained rank-20 SAT refit fitted witnessed points but worsened a common holdout. A second fit allowed at most two changes to the incumbent phases per round and used extra supports. It reduced misses from 2,200 to 2,067 in the same 200,000-point holdout. The replacement has 1,144 patterns and an exact hole. The next finite SAT instance was unsatisfiable within its imposed phase menus and change budget.
- The Harrington search tested actual congruence classes with new moduli up to 800,000 and primes through 73. It fitted all 200,000 training integers and missed 1,964 of 200,000 independent holdout points. The exact witness checker finds a single integer avoiding all 3,067 classes, including 110 mixed additions. A second pass that changed phases of the additions reduced the misses from 3,519 to 3,342 on its own common 350,000-point holdout. Its exact integer witness also survives.
- Three prefix-box configurations covered their 250,000 training points and had exact holes. The 20-coordinate run with heights $h_3=2$, $h_5=h_7=1$ missed 4,855 of 200,000 holdout words. A complete phase model for a restricted rank-12 and arity-4 catalogue finished its bounded run with 1,653 witness constraints and a further hole. The separate rank-8 run freed the unary phases and finished its bounded run with 1,070 constraints. These are incomplete searches of the stated catalogues.

## Replay

Within the Conjecture Killers research directory, the continuation scripts use the previous checkpoint sources in the parent directory. The exact arithmetic and witness checks require Python 3. The search scripts additionally use NumPy and, for the SAT fits, python-sat with CaDiCaL 1.9.5.

Run from the continuation directory.

    python3 crossing_certificate.py
    python3 check_harrington_witness.py harrington_mixed.json
    python3 check_harrington_witness.py harrington_reoptimized.json
    python3 ../check_candidate.py refit_rank20_preserved.json
    python3 prefix_lift.py prefix_candidate.json

Lean 4.36.0 replays the numerical certificate, the payoff and assigned-class lemmas, and the integer exit lemma. Use the previous checkpoint's pinned mathlib revision and put the compiled previous checkpoint Certificate module on the Lean path. The theorem that combines these ingredients is given as a written proof.
