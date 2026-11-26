# Necessary counts for prime-divisible moduli

Let a hypothetical distinct odd covering have $N_3$ moduli divisible by 3 and $N_5$ moduli divisible by 5. Then
$$
N_3\ge18,\qquad N_5\ge11.
$$
There are also stronger bounds if specified small moduli are absent.

| Absent moduli | Lower bound on $N_3$ |
|---|---:|
| 3 | 39 |
| 9 | 19 |
| 15 | 20 |
| 3 and 9 | 53 |
| 3 and 15 | 55 |
| 9 and 15 | 27 |
| 3, 9 and 15 | 76 |

Each bound applies to any finite hypothetical odd cover. The proof uses neither an exponent cap nor an assumption about which other moduli exist.

## 1. A measure on the prime-free fibres

Fix $p\in\{3,5\}$ and factor the period of the family as $p^a M$ with $p\nmid M$. Let $H\subseteq\mathbb Z/M\mathbb Z$ be the set avoiding the classes with moduli coprime to $p$. For each $p$ we construct a probability law $\mu$ on $\mathbb Z/M\mathbb Z$ with
$$
\mu(H)>h_p,\qquad
\mu(b\bmod d)\le W(d):=\frac1d\prod_{q\mid d}\gamma_q
\quad(d\mid M),
$$
where $h_3=7494/10000$ and $h_5=2097/10000$. The constants for $p=3$ are from the schedule in [three_free_loss.py](three_free_loss.py). For $p=5$ use $\gamma_3=2$ and $\gamma_q=10/7$ for all $q\ge7$.

Apply the distortion method of Dai, Li, Li and Yi, especially Lemmas 2.1 and 2.3, Theorem 2.6, formulas (12), (14), (16) and Section 4.3. Use all primes of $M$ in increasing order. The stage at $q$ assigns the classes of the prime-free family whose largest prime is $q$. Its parameter is $\delta_q$ and $\gamma_q=(1-\delta_q)^{-1}$. The stage preserves the preceding marginal and gives the stated bound for a class in its own coordinate conditional on each preceding assignment. Applying those conditional bounds in reverse order yields $W(d)$.

When $p=3$, the initial $q=5$ stage uses $\delta_5=1/4$. The total fraction occupied by distinct powers of 5 is at most $1/4$, so this stage costs zero mass. When $p=5$, condition the 3-coordinate on escaping all classes with moduli powers of 3. These classes occupy at most $1/2$, giving the conditional bound $2/3^e$. Empty coordinates or stages may be padded in the scalar upper comparison.

For a stage at $q$, the comparison uses $D=\prod_{s<q}(1+T_s)$, where $T_s$ are independent with $\Pr(T_s\ge e)=\gamma_s/s^e$ for $e\ge1$. The removed mass is at most
$$
\frac{\gamma_q}{q-1}\,\mathbb E(D-\delta_q(q-1))_+.
$$
For this bound, distinctness allows at most one class with each cofactor and $q$-exponent. The program sums upper bounds on the stage contributions with integer rounding toward $+\infty$ at scale $10^{18}$. Up to 20,000 it uses
$$
\mathbb E(D-t)_+=\mathbb E D-t+\mathbb E(t-D)_+
$$
and replaces factors by $\min(1+T_s,10)$ only in the last term, where this change increases the integrand. Values of the resulting product above the largest retained threshold make zero contribution. Up to $10^7$ the remaining terms use the positive-part cubic bound, which for $\delta_q=3/10$ gives $4000\,\mathbb E D^3/[1701(q-1)^3]$. Beyond $10^7$ we use the bound in Section 4.3 for the $5$-free case and rescale it by the exact ratio of third moments for the $3$-free schedule. The ratio is constant throughout that tail, since all later parameters agree.

| Omitted prime | Through 20,000 | Above 20,000 through $10^7$ | Beyond $10^7$ |
|---|---:|---:|---:|
| 3 | 0.247150176857323885 | 0.003414799652875517 | $\le 0.000001948$ |
| 5 | 0.776079294239838265 | 0.014170653052843397 | $\le 0.000008082310506662$ |

The mass of the union of all prime-free classes is at most the sum of the stage bounds. The complements satisfy the asserted strict margins. This part uses the cited preprint for the comparison and analytic tail. [Dai, Li, Li and Yi, *On the moduli of distinct covering systems*](https://arxiv.org/abs/2611.15110)

## 2. The ternary tree

Work with $p=3$. CRT lets us combine any $3$-adic residue at height $a$ with any point of $H$. Therefore, for every residue $x\bmod 3^a$, the projected classes with moduli $3^e d$ whose 3-adic prefix agrees with $x$ must cover $H$. By the union bound, the sum of their $W(d)$ must reach $h_3$. In this sum we can charge only $h_3$ when $d=1$, since a single such charged class already reaches the threshold everywhere on its prefix.

Represent a modulus $3^e d$ by one token of weight $W(d)$ placed at the corresponding node of the full ternary tree. A token contributes to all leaves below that node. Distinctness permits a weight label $d$ at most once per level, regardless of position. Each path from root to leaf must receive weight at least $h_3$.

The exact algorithm in [weighted_tree.py](weighted_tree.py) relaxes all weights upward to units of $1/10000$. For any $k$ classes at a given level, the weights used can be replaced by the $k$ largest available cofactor weights, in order. Placing these larger weights in the same positions preserves the requirement. The palette is independent of the level. The code finds every required top weight by enumerating $d<12000$ and checking the largest possible omitted weight against the last retained one. In detail, $\gamma_q\le\sqrt q$, so $W(d)\le d^{-1/2}$ for this palette.

The state is the sorted multiset of positive deficits at the current depth, together with the budget of unused tokens. Each deficit is copied to three children. For each choice of $k$, enumerate the residual multiset obtained by placing the $k$ largest weights among the children. Saturated children drop out. Placement of surplus tokens on saturated children can be discarded, since the feasibility question uses a budget of at most the given number. If a level is empty, keep the child with a fixed digit at each current node, delete that digit from all later prefixes, and discard other classes. This preserves coverage with at most the original number of tokens and keeps labels distinct at each depth. Thus a feasible configuration has at most as many levels as tokens.

Two necessary conditions prune states. Each active child needs at least one token in its descendant subtree, including at that child. Also, a weight $w$ placed $e$ levels below the current depth contributes at most $w/3^e$ toward the sum of the current deficits, after averaging descendants uniformly. The sum of the best remaining discounted weights, with at most one copy of each per level, bounds the total contribution.

The enumeration excludes all budgets up to 17. It also finds a feasible relaxed state at 18. The relaxation permits independent placements of the projected weights.

## 3. Integrating the ternary inequalities

Average the path inequalities uniformly over the 3-adic coordinate. A modulus $m=3^e d$ contributes $3^{-e}W(d)$, with the same truncation to $h_3$ for $d=1$. Thus the sum of these weights over the 3-divisible moduli reaches $h_3$. For each proposed set of absent moduli, [three_volume.py](three_volume.py) enumerates all eligible $m\le100000$, sorts their rational weights and certifies that the best sum one below the stated lower bound is strictly less than $h_3$.

For each scheduled prime, $\gamma_q^4\le q$, and $(10/7)^4\le5$ handles all unscheduled primes. Thus any $m>100000$ has weight at most $m^{-3/4}$, because $W(d)\le d^{-3/4}$ and $3^{-e}\le (3^e)^{-3/4}$. For each tested count that tail bound is smaller than the last weight used in the sum. This handles arbitrary modulus size.

## 4. The five first-level fibres

For $p=5$, every first-level row needs at least one class with modulus divisible by 5. Suppose there are at most nine such classes. No row contains more than five. A row with five classes can arise only if the other four rows have one class each. A singleton must have 5-adic exponent one, since otherwise some second digit has no matching class. Its cofactor must be in $\{1,3,9\}$, as every other cofactor has weight at most $10/49<h_5$. Distinctness permits only three singleton rows, so every row has at most four classes. In each row choose a second digit avoiding all classes with 5-adic exponent $\ge2$, if the period has such a digit. The exponent-one projections thus cover $H$ in each row. We can discard all deeper classes, and the cofactor labels of the remaining projections are distinct globally.

A singleton with cofactor 9 would put $H$ inside a class $R_9$ modulo 9. Each nonspecial cofactor $d\notin\{1,3,9\}$ has intersection with $R_9$ of mass at most $20/441$ if it contains a prime other than 3. For pure powers of 3, the bound is $2/27$ if $d=27$, and at most $2/81$ otherwise. The total for any three nonspecial classes is at most $2/27+40/441<h_5$. With three singleton rows, every other row is nonspecial and one has at most three classes. With two singleton rows including 9, at most one of the other rows uses the unused special cofactor, and some row of size at most three has none. With only one singleton of cofactor 9, all other rows have size two, so at least one has neither of the two unused special cofactors. This excludes a singleton of cofactor 9 in every case.

If a singleton has cofactor 3, then $H\subset R_3$ for a class $R_3$ modulo 3. A two-class row can then cover $H$ only if it uses cofactor 1, cofactor 9, or both 7 and 21. To see this, intersect the projections with $R_3$. Excluding $1,3,9,7,21$, each intersection has mass at most $20/231$, so any two of those labels fall short. A projection with $d=7$ or 21 is contained in a class $A_7$ modulo 7 within $R_3$. Put $u=10/49$ and $v=10/77$. If the partner label contains any prime $q\ge11$, that projection is contained in a class modulo $q$, whose conditional mass given all preceding coordinates is at most $v$. The union with $A_7$ inside $R_3$ has mass at most $(2/3)(u+(1-u)v)<h_5$. If the partner is a pure power of 3 of exponent at least three, sum separately over that class and its complement in $R_3$. The conditional bound at prime 7 gives at most $2/27+(2/3-2/27)u<h_5$. In the remaining case the partner contains 7, with exponent at least two or a 3-adic exponent at least two. Its intersection with $R_3$ has mass at most $20/441$. Adding the $A_7$ bound still falls short.

With a single singleton of cofactor 3 there are four double rows, but the three allowed options use disjoint fixed labels and can occur in at most three rows. With two singleton rows they must use 1 and 3. There are either three double rows or two double rows and one triple row. Three double rows would need three options, and only cofactor 9 and the pair 7, 21 remain. With two double rows, they must use those two options. The row with 7 and 21 restricts $H$ to $R_3$ and at most two classes modulo 7. In the triple row none of $1,3,9,7,21$ occurs. A label with prime factor $q\ge11$ contributes at most $(2/3)(2u)v$ inside that restriction, by the conditional bound at $q$. A pure power of 3 contributes at most $(2/27)(2u)$. Any remaining label contributes at most $20/441$, by its intersection with $R_3$. Each bound is at most $20/441$, so the triple row falls short.

The only remaining profile is one singleton with cofactor 1 and four double rows. At least two double rows use neither 3 nor 9. For such a row each cofactor $d$ must have $W(d)\ge h_5-W(7)$ because $W(7)$ is the largest available weight. The bound $W(d)\le 2/\sqrt{3d}$ implies $d\le43000$. This follows from $\gamma_q\le\sqrt q$ except for $q=3$, which supplies the extra factor $2/\sqrt3$.

[The exact two-row checker](five_pairs.py) first filters pairs of cofactor pairs by summing the four weights of the cross least common multiples. Whenever this sum reaches $h_5$, it checks the conditional mass of the intersection of the two row unions directly for all phases. At each prime it enumerates possible agreement masks for the tracked classes, grouping coordinate residues with the same mask. A translation allows it to fix one residue at maximum depth. Given later values, the conditional expected value at this coordinate is at most the result of allocating mass to groups in decreasing order of value, with each residue capped at $\gamma_q/q^e$ at depth $e$. This upper bounds even laws in which later coordinates depend on earlier ones. The program computes backward over the coordinates using exact fractions.

The only compatible nonspecial pair of rows is $(7,33)$ and $(11,21)$. Three nonspecial pairs are therefore impossible, and the other two rows must separately use 3 and 9. Applying the same conditional mass check to these two nonspecial rows together with a class modulo 9 bounds the portion inside that class by $2320/33957$. The other cofactor paired with 9 differs from $1,3,7,9$ and has weight at most $W(21)=20/147$. Their sum is below $h_5$. This excludes the final row profile, proving $N_5\ge10$.

## 5. Excluding ten 5-divisible moduli

Use a second law for the same 5-free family and the same uncovered set $H$. Change only $\delta_{11}$, from $3/10$ to $1/5$, so the cap factor at 11 becomes $5/4$. The distortion checker gives upper bounds $0.778268846599072937$ through 20,000, $0.013211858866950087$ through $10^7$, and less than $0.000007536$ beyond $10^7$. This law gives $H$ mass greater than $h'_5=2085/10000$. All its cofactor caps are at most their baseline values. The adjusted pair enumeration uses $h'_5$ and cofactor limit 70,000, which suffices by the same upper bound $2/\sqrt{3d}$. It excludes **every** pair of two nonspecial double rows.

Suppose exactly ten moduli are divisible by 5. Every first-level row is nonempty. A row of size at least five would force either four singleton rows, which is impossible, or the profile $1,1,1,2,5$. In the latter case the three singleton cofactors include 9, and the double row with no special label fails by its intersection with $R_9$. In all other profiles every row has at most four classes, so the second-digit argument discards all classes with exponent at least two. We already excluded nine or fewer classes, so this leaves ten exponent-one classes.

If there are no singleton rows, there are five double rows. At least two are nonspecial, excluded by the adjusted law. Any profile with a singleton cofactor 9 is also impossible. As in Section 4, some row of size at most three has no special label and fails to cover $H\subset R_9$. To check the count, the possible profiles are $1,2,2,2,3$, $1,1,2,2,4$, $1,1,2,3,3$, $1,1,1,2,5$, and $1,1,1,3,4$. Each has a size-two or size-three row unprotected by an unused special label.

If the only singleton cofactor is 3, three double rows force all three options from Section 4, including the pair 7, 21. The triple row then fails under the same bound $20/441$ per class applied on $R_3$ and the union of the at most two specified classes modulo 7. With two singleton cofactors, they are 1 and 3. If the profile is $1,1,2,2,4$, both double-row options must be used and the remaining size-four row fails, because $4(20/441)<h_5$. If the profile is $1,1,2,3,3$, the double row must use 9. Otherwise it uses 7 and 21, and a triple row without 9 fails by the same intersection estimate.

It remains to handle these two profiles.

1. **Singleton cofactors 1 and 3, one double and two triples.** The double row uses cofactors 9 and $D$. The triple row avoiding label 27 gives $\mu(H\cap R_9)\le60/441$ under the baseline law. Since $H\subset R_3\cap(R_9\cup[D])$, with $[D]$ denoting the projected class, we need $W(\operatorname{lcm}(3,D))>h_5-60/441$. Inspecting the prime factors gives $D\in\{7,11,13,21,27,33,39\}$ as an upper list. In fact, for any remaining cofactor the bound is at most $20/273<h_5-60/441$. Each other projected class with label $d$ contributes at most
   $$
   \min\!\big(W(\operatorname{lcm}(3,d)),\,W(\operatorname{lcm}(9,d))+W(\operatorname{lcm}(3,D,d))\big).
   $$
   The two triples jointly need six distinct labels and total contribution greater than $2h_5$. For each $D$, the exact sum of the six largest eligible upper bounds is below $2h_5$. The largest of these sums is $513718/1324323$. The checker enumerates through 10,000 and upper-bounds each omitted cofactor by $1/50$ using $W(d)\le 2/\sqrt{3d}$.
2. **Only singleton cofactor 1, three doubles and one triple.** The adjusted law permits at most one nonspecial double, so one double uses 3 and another uses 9. The nonspecial double gives $\mu(H\cap R_9)\le 2/27+20/441$ since its two labels are distinct. Therefore the cofactor paired with 9 must have weight greater than $h'_5-2/27-20/441$. Under the adjusted caps the only eligible labels are $7,11,13,21$. The exact two-row test over all phases leaves three possibilities for the nonspecial double and the row containing 9:
   $$
   (21,27)\text{ with }(9,7),\qquad
   (7,27)\text{ with }(9,21),\qquad
   (7,63)\text{ with }(9,21).
   $$
   For any triple-row label $d$, its intersection with the two row unions has mass at most both $W(d)$ and the sum of $W(\operatorname{lcm}(a,b,d))$ over the four cross pairs $(a,b)$ of these rows. The triple row must use three distinct previously unused labels. The largest possible sum of their upper bounds is at most $1780/14553<h'_5$. Here the checker enumerates through 5,000 and bounds each omitted cofactor by $1/50$.

The two profiles are impossible, proving $N_5\ge11$.

## Replay and priority

Run these commands from the continuation directory in the pinned Lean 4.36.0 environment.

    python3 three_free_loss.py
    python3 three_free_loss.py --excluded 5 --baseline
    python3 weighted_tree.py --prime 3 --max 18
    python3 three_volume.py
    python3 five_pairs.py
    python3 three_free_loss.py --five-pair-schedule
    python3 five_pairs.py --adjusted
    lake env lean FibreCertificate.lean

Lean checks the stated rational margins and the seven-class row count. The ternary search, projected pair enumeration and numerical summations are exact Python computations. The linking arguments, full distortion comparison and infinite-prime tail are outside the Lean certificate.

The prior necessary divisibility conditions for the period $Q$ include $3\mid Q$ (Hough and Nielsen), $9\mid Q$ or $15\mid Q$ (Balister, Bollobás, Morris, Sahasrabudhe and Tiba), and $45\mid Q$ with minimum modulus at most 9 (Dai, Li, Li and Yi). I found no matching direct fibre-count bounds in those references or the public claim ledger examined. Priority remains provisional. [Erdős Problems #7](https://www.erdosproblems.com/7) · [Public claim ledger](https://erdosproblems.ai/wiki/problems/covering_systems/E0007/claims) · [Dai et al.](https://arxiv.org/abs/2611.15110)
