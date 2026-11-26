# Operation Selfridge checkpoint 3

## Status

Erdős Problem 7 remains unresolved in this checkpoint. The results below exclude a construction template through 19 prime coordinates and exclude a class of repairs to a specific published near-cover. The valuation-box lift from checkpoint 2 is sufficient for an odd integer cover. The reduction runs from the valuation boxes to the existence of an odd integer cover. Lean checks the numeric inequalities, the one-coordinate comparison, and a CRT assembly lemma. The complete distortion argument and the residue verification of Harrington's seed are supplied as a written proof and exact Python checks.

## Literature and priority

- Balister, Bollobás, Morris, Sahasrabudhe and Tiba established the square-free exclusion and the use of hyperplanes with distinct supports. The alphabet in their square-free theorem is the list of odd primes. The valuation alphabets below have sizes one smaller. [Square-free paper](https://doi.org/10.2140/ant.2021.15.609)
- Dai, H. Li, J. Li and Yi give the stronger unrestricted necessary conditions $45\mid\operatorname{lcm}$ and minimum modulus at most 9. The two estimates below use their scalar and joint convex comparison. [November 2026 preprint, Sections 2–5](https://arxiv.org/abs/2611.15110)
- Mian and Siddique formalized an LCM exclusion through 10,000. Schroeder's rank-nine preprint reports a separate exclusion for covers with at most eight support primes and arbitrary exponents. The latter concerns integer covers and is separate from the valuation alphabet result here. [Mian–Siddique](https://arxiv.org/abs/2607.25628) · [Schroeder proof companion](https://michaelschroeder.ai/research/NinePrimeSupport/companion)
- The Archivara and Aristotle claim relies on the unproved `HoughNielsenGoodFibre`. The Lee claim used a false inequality as an axiom. [Good-fibre claim](https://erdosproblems.ai/wiki/problems/covering_systems/E0007/claims/2026_01_11_gebyjaff) · [Lee claim](https://erdosproblems.ai/wiki/problems/covering_systems/E0007/claims/2026_05_02_lee)
- The CRT assembly lemma in `Closure.lean` is a variant of Nathan McNew's almost-covering extension. It permits any odd $q>1$ coprime to the hole modulus, when the input moduli avoid divisibility by $q$. The assembly idea is prior work. [McNew, Corollary 4.8](https://erdosproblems.ai/wiki/library/covering_systems/mcnew_2026_densities_covering_numbers_abundant_numbers/corollary_4_8)
- The closest located work includes the quarter-density tail criterion and Trureturing's block-saturation criterion. Its cited degree-two example permits arbitrary {3,5,7} heads and tail primes at least 37. The six-prime calculation here starts at 19 and uses the occupied labels of a specified seed. The present certificate concerns the particular 2,471-class family reconstructed below, covering arbitrary exponents with the stated restrictions on new moduli. Priority for either application below remains provisional. [Exact-loss claim](https://erdosproblems.ai/wiki/problems/covering_systems/E0007/claims/2026_10_19_plasma_ai) · [Trureturing block-saturation report](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/erdos7-odd-covering/problem-details/06-block-saturation-and-the-actual-crossing-budget.md)

## 1. The valuation boxes with at most 19 prime coordinates fail

Let $p_1,\ldots,p_r$ be distinct odd primes, $r\le19$, and let the $i$-th alphabet have $p_i-1$ values. A cylinder fixes a nonempty subset of coordinates to specified individual values. A covering by cylinders with pairwise distinct fixed coordinate sets is impossible.

### Reduce the alphabets and count labels

Sort the primes. Restrict the $i$-th coordinate to a subset with the alphabet size for the $i$-th smallest odd prime, and append free coordinates to make 19 if necessary. Discard empty intersections. The resulting alphabet sizes are all at least two, so every surviving fixed coordinate stays fixed. A cover would be preserved.

Add any missing single-coordinate cylinders and delete the value of each such cylinder from its alphabet. At prime 3 the alphabet now has one value. Delete that coordinate. On each nonempty support in the remaining 18 coordinates, there can be at most two cylinders, one from the original support and one from that support with the 3-coordinate adjoined. The only cylinders that could project to an empty support have already been deleted. For each remaining coordinate, remove the values of its at most two single-coordinate cylinders. Remove extra arbitrary values if needed to leave exactly $s_i=p_i-3$ values. Now every cylinder has at least two fixed coordinates, with multiplicity at most two per support. The sizes $s_i$ are the entries of `stages` in `Certificate.lean`.

### Distortion and the comparison recurrence

Order the resulting 18 coordinates as in the certificate. Stage $i$ contains cylinders whose last fixed coordinate is $i$. Let $\alpha_i(x)$ be the fraction of this coordinate's fibre covered by its stage, for a fixed prior prefix $x$. Use the BBMST distortion update with parameter $\delta_i$ and uniform reference on the coordinate. It keeps the total mass of each prefix fibre and gives its covered part conditional mass $g_i(\alpha_i)=(\alpha_i-\delta_i)_+/(1-\delta_i)$. If $\alpha_i\le a$, the mass on any one value is at most $\kappa_i(a)/s_i$, where $\kappa_i(a)=1/(1-\min(a,\delta_i))$. These statements follow by putting mass $1/(s_i(1-\alpha_i))$ on each uncovered value and zero on covered values when $\alpha_i\le\delta_i$. Otherwise put mass $1/(s_i(1-\delta_i))$ on each uncovered value and distribute the remaining mass uniformly over the covered values. Each earlier stage keeps its mass under subsequent updates, so an upper bound less than one for the sum of the stage masses disproves coverage.

For clarity, work backward on a vector of nonnegative availability weights $z$, indexed by all original cylinders still to be processed. At an actual prefix the entries are zero or one, according as the cylinder's restrictions on earlier coordinates fail or hold. Bound the current $\alpha_i$ by $a=s_i^{-1}\sum z_j$ summed over current-stage cylinders. Split the other weights into $A_0$ for cylinders free in the current coordinate and $A_1$ for the rest, padding with zeros on the complementary slots. Let $F$ bound future losses and be increasing with increasing differences in nonnegative directions. Write $B=[F(A_0+A_1)-F(A_0)]/s_i$ and $c=(1-\delta_i)^{-1}$. The one-coordinate comparison gives an upper bound $F(A_0)+\kappa_i(a)B$ for continuation. Indeed, each fixed value is hit with conditional probability at most $\kappa_i(a)/s_i$. Telescoping the increments of $F$, an increment from a matching cylinder is at most the corresponding increment when all earlier cylinders in the telescope match. `Comparison.lean` proves this statement for finite fibres.

Dai et al.'s joint update (Lemma 3.2) therefore bounds current plus future loss by

$$
 g_i(a)+F(A_0)+cB-(c-\kappa_i(a))\min(B,1/c).
$$

The binary-coordinate case uses their proof with only exponent slots 0 and 1 and the uniform atom bound $1/s_i$. In detail the update is the maximum of $g_i+F(A_0)+\kappa_i(a)B$ and $g_i+F(A_0)+cB-(c-\kappa_i(a))/c$. For fixed $a$, both branches are increasing, separately convex and supermodular in the weights. Their difference is $(c-\kappa_i(a))(B-1/c)$, which is increasing in the weights. For two points whose maxima use different branches, supermodularity of the first branch and monotonicity of the difference at their coordinatewise maximum prove supermodularity of the maximum. Separate convexity passes to the maximum. For fixed weights, the derivative in $a<\delta_i$ is $\kappa_i(a)^2\min(B,1/c)\le c$. Above $\delta_i$ the derivative is $c$. Increments in $a$ are increasing in the weights because their only weight-dependent term is a nonnegative multiple of $\min(B,1/c)$. These properties give increasing differences in nonnegative directions by splitting them into single-coordinate increments. The update also stays increasing. This justifies backward induction from the zero function, and substituting the nonnegative linear maps for $a,A_0,A_1$ preserves these properties.

In this comparison, monotonicity allows inserting both slots for every support of size at least two. At each comparison step all cylinders fixing that coordinate either survive together or vanish together. If $t$ previous comparison coordinates survived, the load of a stage of size $s$ is $2(2^t-1)/s$. Exactly the nonempty subsets of the $t$ successful coordinates can join the current coordinate. The two continuation values depend on whether the current coordinate fails or survives, giving $t$ or $t+1$. Thus the update above gives the backward table implemented by `certificate.py` and independently by `Certificate.lean`. The initial value is less than $9991/10000$, proving the claim.

### Construction search past the bound

The rank-20 run used 200,000 training points and 200,000 separately generated holdout points. It chose 721 patterns. All training points were covered. The holdout had 2,281 misses. `check_candidate.py` checks, by integer comparisons alone, that the recorded point is an exact hole. The holdout number is a sample statistic. The earlier rank-12 exact count attempt exceeded the process memory budget and contributed no result. The exact witness rules out this saved rank-20 layout. Higher-rank layouts and general prime-power CRT cylinders remain open.

## 2. A repair obstruction for Harrington's family

Let $\mathcal H$ be Harrington's distinct near-cover with the class $1\pmod3$ retained and the duplicate modulus-3 class removed, using the explicit valuation reconstruction linked below. All its moduli are supported on $P=\{3,5,7,11,13,17\}$. Retain its 2,471 classes and add any finite family of classes with odd, pairwise distinct moduli, also distinct from the seed moduli. If every added modulus has at most one prime divisor outside $P$, an integer still escapes. The additions supported entirely on $P$, the number of fresh primes and all prime exponents are arbitrary.

[Harrington 2015](https://doi.org/10.1142/S179304211550075X) · [Explicit valuation reconstruction](https://erdosproblems.ai/wiki/research/leads/odd_covering_distortion/support_concentration)

### A product of residual points

Use the following independent conditions on the six old prime coordinates.

| Prime | Allowed condition |
|---|---|
| 3 | Residue 2 modulo 3 |
| 5 | Valuation 0 or 1 and first nonzero digit in `{2,3,4}` |
| 7 | Valuation 0 or 1 and first nonzero digit in `{2,4,5,6}` |
| 11 | Residue 2 through 10 modulo 11 |
| 13 | Residue 2 through 12 modulo 13 |
| 17 | Nonzero modulo 17 |

The condition at 3 defeats every seed class with a 3-factor. The conditions at 5 and 7 defeat their pure powers and the mixed classes with 5-digit 4 and 7-digit 3. The first two closing families require either a zero residue at their auxiliary prime or a matching $j\ge2$ and divisibility by $5^j$ or $7^j$. The 17-closing family requires a zero at 17 or divisibility by 3. Thus every point in this product misses the seed. `harrington_seed.py` also independently builds the congruences and checks CRT incompatibility with this product for each of the 2,471 classes.

Put the uniform measure on the allowed residues, with all higher digits uniform, taking finite coordinates at any sufficiently large depth for a given candidate extension. A single residue modulo $p^e$ has probability at most $u_p(e)=1/(s_p p^{e-1})$, for $e\ge1$, with

$$
(s_3,s_5,s_7,s_{11},s_{13},s_{17})=(1,18/5,32/7,9,11,16).
$$

At 5 this uses $3\cdot5+3=18$ allowed residues modulo 25. For a residue at depth one there are at most 5 lifts, and at depth two or higher each branch has the indicated uniform mass bound. At 7 the corresponding number is $4\cdot7+4=32$. Set $u_p(0)=1$.

### Condition away the single-coordinate additions

For a head modulus $d=\prod_{p\in P}p^{e_p}$, define its effective support to contain 3 if $e_3\ge2$, and to contain each other prime if $e_p\ge1$. The original ternary digit is fixed, so an exponent of 1 at 3 contributes no effective coordinate dependence. The residue probability of this label is bounded by $w(d)=\prod_{p\in P}u_p(e_p)$. The empty effective support can only arise from 1 or 3, and these two moduli are unavailable.

For each nonempty support $S$, let $W(S)$ sum $w(d)$ over all labels of effective support $S$ except those occupied by the seed. These sums are geometric. The factor at 3 is $2$ on exponent slots 0 and 1 combined, and $1/2$ on the slots $e_3\ge2$. At other primes, the factor for present support is $p/[s_p(p-1)]$. Subtract the weights of all occupied numerical labels, irrespective of their phases. This subtraction uses the global distinctness of the proposed extension.

For each $p\ne3$, the head-only additions with effective support $\{p\}$ depend on their own coordinate. Condition each such coordinate on escaping its own group. The law stays a product, and the marginal upper cap at $p$ grows by at most $1/[1-W(\{p\})]$. Each such axis group now has zero mass. Multiply the cap of every other support by the product of these factors at the coordinates it uses. Call the resulting group bounds $w_S$. Equivalently, the conditioned atom bounds have the original form with the corresponding $s_p$ multiplied by $1-W(\{p\})$. The 3-adic axis is handled by the remaining group bounds, leaving the first ternary digit law intact.

### Bound the whole old-prime union

Let $E_S$ be the union of the remaining head-only classes of effective support $S$. These group events have a dependency graph with an edge exactly when their supports intersect. An event is independent of the joint sigma algebra of all groups with disjoint support.

For coordinate universe $U$, define $Q(U)$ to be the alternating independent-set sum of the groups supported within $U$, using the outward-rounded probability caps $w_S$. With $v\in U$, partitioning independent sets by the group containing $v$ gives

$$
Q(\varnothing)=1,\qquad
Q(U)=Q(U\setminus\{v\})-\sum_{v\in S\subseteq U}w_S Q(U\setminus S).
$$

The checker finds $Q(U)>0$ for all 64 universes. This also proves positivity for every subset of the groups. Induction on the coordinate universe shows that adjoining a group of support $S$ lowers its family's independent-set polynomial by $w_S$ times a nonnegative polynomial on the strictly smaller universe $U\setminus S$. Thus each subfamily has polynomial at least the computed value for the full family on its universe.

If $A$ is a group subfamily, write $Q_A$ for its positive polynomial and $P_A$ for the probability of avoiding its events. For any $i\in A$, let $B$ delete $i$ and its neighbours from $A$. Independence gives $P_A \ge P_{A\setminus\{i\}}-w_i P_B$. The polynomial satisfies $Q_A=Q_{A\setminus\{i\}}-w_i Q_B$. Induct on $|A|$ to prove $P_A/P_{A\setminus\{i\}}\ge Q_A/Q_{A\setminus\{i\}}>0$. The induction applied successively along the chain from $B$ to $A\setminus\{i\}$ gives $P_{A\setminus\{i\}}/P_B\ge Q_{A\setminus\{i\}}/Q_B$, which proves the induction step. Consequently $P_A\ge Q_A$ by multiplying along a chain from the empty family. This is Shearer's bound, used here with the intersection graph of the six effective coordinate supports. The exact lower bound for old-only survivor mass exceeds $0.3223$.

### Bound the blocked head points for each fresh prime

For a new prime $q\ge19$, group the added moduli having $q$ as their only new prime. They are $q^k d$ with $d$ supported on $P$ and $k\ge1$. At a head point $x$, put

$$
L_q(x)=\sum_{(k,d)\ \mathrm{used}}q^{-k}\mathbf 1_{\{x\equiv r_{k,d}\ (\mathrm{mod}\ d)\}}.
$$

The $q$-fibre fraction covered by these classes is at most $L_q(x)$. If the whole fibre is blocked then $L_q(x)\ge1$.

For a convex increasing function of the load, align the congruence indicators on each coordinate in a comparison distribution, using the new marginal caps. In one coordinate, order the projected indicators by their cap from largest to smallest. Telescope the increments of the convex function, bounding each active increment by its value when every preceding indicator is active. The cap times each upper increment is the expected increment for nested indicators with exactly those caps. Repeat independently over the six coordinates. Write independent $T_p$ with $\Pr(T_p\ge e)=1/(s_p' p^{e-1})$ for $e\ge1$, where $s_p'$ incorporates the axis conditioning. Set $D=\prod_{p\in P}(1+T_p)$. Distinctness gives comparison load at most $D/(q-1)$ because each pair $(k,d)$ is used at most once. This is the scalar comparison of Dai et al. with the displayed marginal bounds.

For each $q\le2500$ and integer $0\le t<q-1$, use the convex payoff $(L_q-t/(q-1))_+/(1-t/(q-1))$, which is at least one on the blocked event. The blocked probability is at most $\mathbb E(D-t)_+/(q-1-t)$. Use the minimum over these $t$. For $q>2500$, use the square payoff, giving $\mathbb E D^2/(q-1)^2$. Compute the positive-part expectations via

$$
\mathbb E(D-t)_+=\mathbb E D-t+\sum_{d<t}(t-d)\Pr(D=d).
$$

The first and second moments factor by independence. The checker propagates the distribution below the largest threshold with outward integer rounding. Products larger than the threshold can be discarded because subsequent factors are at least one. It sums primes through $300000$ and includes all integer values $n=q-1\ge300000$ above the cutoff, using $n^{-2}\le1/[n(n-1)]$. The exact aggregate fresh-prime blocked probability is below $0.3223$.

### Combine the choices

Under the product law after axis conditioning, the union of the fresh-prime blocked sets has strictly smaller mass than the set of old-only survivors. Choose a head point outside every old-only class and every blocked set. For each fresh prime choose an uncovered residue at the largest exponent used at that prime. The Chinese remainder theorem combines these choices and the head residue into one integer. It misses the original seed and all additions.

Any completion retaining this seed therefore needs a new modulus involving two or more primes outside $P$. The conclusion concerns covers that contain the original seed classes.

## Replay

The pinned toolchain is Lean 4.36.0 with Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. In an environment with Lean and Mathlib available:

```sh
lake update
lake exe cache get Mathlib/Tactic.lean Mathlib/Data/Int/ModEq.lean
lake env lean Certificate.lean
lake env lean Comparison.lean
lake env lean Closure.lean
```

The exact arithmetic and witness checks use Python's standard library. Only rerunning the heuristic needs NumPy.

```sh
python3 certificate.py
python3 harrington_seed.py
python3 harrington_obstruction.py
python3 check_candidate.py
python3 search_box.py --rank 20 --output rank20_candidate_replayed.json
python3 check_candidate.py rank20_candidate_replayed.json
```
