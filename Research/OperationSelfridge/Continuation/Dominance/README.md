# Two unary profiles in the released rank-24 search

Consider the **3,303 mode vectors** in the released rank-24 catalogue, with heights 2 at 3, 1 at 5 and 7, and 0 at the other 21 primes. Give each used vector any legal phase. If this catalogue admits a covering of the full atom product, it admits one with either of just two fixed unary layouts. Both representatives have now produced improved finite fits and exact uncovered products. Existence in each representative remains open. The rank-24 catalogue includes the prime 7. These two profiles concern a different question from the two no-7 affine orbits modulo 45.

## Lossless unary normalization

On a prime coordinate of height $h$, represent the atom $(r,d)$ by the $h$ base-$p$ digits of $r$, least significant first, followed by $d-1$. The first $h$ levels have radix $p$, and the last has radix $p-1$. A fixed mode at level $e\le h$ selects one prefix of length $e$; the variable mode selects an entire word. A shallow and deep selected prefix are disjoint or the shallow contains the deep one.

Fill any unused unary slots if the catalogue allows omission. Scan the unaries within each coordinate from shallow to deep. Whenever the current cylinder is contained in a previously selected cylinder, all of its old points are already covered. Move its phase to a position disjoint from every preceding cylinder. This preserves every previously covered word in the entire product while leaving every mixed slot unchanged.

For a fixed height level $e$, the number of available positions after selecting one disjoint cylinder at each previous level is

$$
p^e-\sum_{d=1}^{e-1} p^{e-d}.
$$

For the variable mode it is $p^h(p-1)(1-\sum_{d=1}^h p^{-d})=p^h(p-2)+1$. Both counts are at least two for every odd prime, including $h=0$. Fewer preceding cylinders leave at least as many choices. Consequently a full unary menu with one prohibited value in the forced-change slot still permits this normalization, provided the initial assignment already satisfies that inequality. This is exactly the restriction used by the released SAT repair. The normalized SAT path supplies every unary phase, deletes the single prohibited value, and forbids compatible ancestor/descendant choices. Its mixed phase menus and repair windows remain restricted. The optimization only scores normalized proposals. The legacy runner continues to support exact reproduction of earlier experiments.

The same idea frees mixed slots. Let $R_j$ be the set of atoms left by the normalized unaries at coordinate $j$. A mixed pattern is already covered by their union precisely when one of its coordinate cylinders misses $R_j$. Indeed the intersection with the surviving product is a product of the local intersections. Moving such a slot arbitrarily preserves all previous atom coverage. We choose replacement phases meeting every relevant $R_j$. The replacement can still coincide with pieces of other mixed patterns.

## Why exactly two profiles remain

Permute the children of every node of a coordinate tree independently. This maps leaves bijectively, preserves prefixes and their lengths, and gives a permutation on the phases of each mode. Taking the product over coordinates relabels an entire pattern by changing its phase in each coordinate. The mode vector, its support, the catalogue and the truth of every matched point/pattern incidence are preserved. Any prescribed consistent map of finitely many paths extends by pairing unused children at each matched node. The invariant for these labelled paths is their pairwise common-prefix lengths. These are combinatorial symmetries of the finite atom model. Integer representatives, residues of auxiliary primes and arithmetic affine equivalence have no role in the relabelling argument.

At height zero, move the lone unary leaf to phase 0. At height one, move the fixed first digit to 0 and the variable atom to root 1, digit 1, encoded as $p-1$. At the ternary height-two coordinate, move the fixed first digit to 0 and the depth-two prefix to residue 1. There are then precisely two profiles.

| Profile | Variable root and nonzero digit | Encoded phase | Sizes of the two surviving first-digit fibres |
|---|---|---:|---|
| Sibling | $(4,1)$ | 8 | 3 and 6 |
| Third branch | $(2,1)$ | 4 | 4 and 5 |

In the sibling profile, the variable root shares its first digit with the depth-two prefix. Its second digit must be different. In the other profile, the variable root uses the remaining first digit. In either case the unused child permutations carry all admissible phases to the displayed representative. Equality of first digits separates the two profiles. Of the 180 legal normalized ternary layouts, 72 are siblings and 108 use the third branch. The corresponding counts at 5 and 7 are 80 and 252. The remaining factors each have $p-1$ choices. Altogether $20,971,416,596,336,980,700,452,757,742,551,040,000,000$ normalized raw unary assignments reduce to two representatives. [Exhaustive local leaf-permutation checks](orbit_counts.txt)

The same classification works for any fixed labelled list of odd coordinate primes with heights at most two, whenever every unary mode occurs and all phases of each selected shape are permitted. With $k$ height-two coordinates the normalized unary layouts have exactly $2^k$ orbits under the independent tree permutations. At an odd prime $p$ of height two, take fixed phases 0 and 1. Sibling and third-branch variable roots have representatives $p+1$ and 2, each with exit digit 1. All three branches exist even at $p=3$, and first-digit equality distinguishes the two types independently at every height-two coordinate. Increasing the number of height-zero or height-one coordinates adds no unary profiles.

For higher finite heights there is an exact counting recurrence. At a node of depth $i$, let $D$ be the set of distinct remaining lengths of the marked paths in its subtree, measured from this node. Let $N_i(D)$ count their disjoint configurations up to rooted tree permutations. An empty set and the singleton $\{0\}$ each contribute 1. A set containing 0 and any other length contributes 0. Otherwise split $D$ into an unordered partition $\pi$ of at most $b_i$ nonempty blocks, where the child radix $b_i$ is $p$ before the final level and $p-1$ at the final level. Then
$$
N_i(D)=\sum_{\pi}\prod_{B\in\pi} N_{i+1}\bigl(\{d-1:d\in B\}\bigr).
$$
Every occupied child contributes one block, and independent subtree symmetries act inside its block. Conversely, a partition and a choice for each block construct one orbit. No division by a factorial is needed because each selected unary length occurs once and the partition is unordered. This statement concerns the finite prefix model. It gives no tail estimate for arbitrary integer moduli.

A global cover satisfies every fixed labelled observation, so it is valid to search both canonical profiles with a bank of necessary point constraints. Transport by the tree map is needed when claiming that a *particular partial layout* retains its coverage of a particular bank. Fixed mixed phases, externally restricted phase menus, historical forced-change inequalities, and selected optimization windows can break the symmetry. We used the two-profile reduction for full-phase catalogue existence and for initializing a separate canonical branch. In that branch, switching the ternary atom between profiles is an ordinary heuristic move, followed by a new exact check of all required observations.

## Computation and exact counterexamples

All point counts below refer to the original labelled coordinate interpretation. The independent 32,768-word diagnostic sample is uniform on the full atom product. Its score was never used to pick a phase during these runs.

| Released layout | Redundant unary moves | Mixed slots hidden after normalization | Original archive misses after both repairs | Diagnostic misses, original → unary → mixed |
|---|---:|---:|---:|---|
| Latest | 2 | 1,343 | 0 / 3,562 | 1,497 → 1,330 → 274 |
| Scored incumbent | 4 | 160 | 0 / 3,562 | 749 → 282 → 205 |

On the latest layout the ternary variable changes from 12 to 2, then the septenary variable changes from 25 to 0. On the scored layout the changes are ternary depth two 0 → 1, ternary variable 0 → 4, quinary variable 0 → 7, and septenary variable 0 → 6. Both normalized layouts use the third branch. Every relocated mixed slot is certified hidden in its old position. Both corrected families strictly improve the respective original layouts by the full-product inclusion argument and by recovering the missed original observation. An original and a repaired layout can have different class counts in the per-root CRT generator.

After these lossless moves, coordinated mixed-phase changes used weighted coordinate ascent. An exact one-slot score gives previously saved points priority over every sampled word combined. Rephasing live slots during this later stage may lose unobserved points. The 8-proposal branch included two complete-unary SAT repairs with a checked forced small-prime change. A second 6-proposal branch used 65,536 probes per round on the surviving unary product while retaining the normalized scored incumbent's third-branch unaries. A third 6-proposal branch made the sibling profile canonical, imported the entire cumulative bank and continued with the same training size. The best full-product diagnostic counts seen in the latter two runs were 126 and 160 misses in 32,768 respectively. All 20 proposals covered every point required at the time of their submission. All 20 have an exact escaping integer and a certified escaping product. [Raw diagnostic counts](holdout.txt) · [Exact replay results](verified.txt)

For each failed proposal, we saved a whole uncovered product, 48 concrete members, their canonical arithmetic witnesses, and the phase changes required to reconstruct the model. Before the full-product test, the separator searches previous products for a point missed by the **union** of the current patterns. It stops at the first counterexample; discharging a product requires that every point be covered, and different patterns may cover different points. The final cumulative bank in `sibling.json.gz` contains 4,526 labelled observations and 4,525 distinct integer representatives, including all of the pre-existing bank. The last sibling candidate covers all 4,478 previous observations. Its escaping product contains $46,362,929,694,333,046,099,329,024,000$ words. Its generator defines 31,581,280,406 congruence classes. The archive also retains the inherited products from the other two runs.

The dominance principle is elementary set inclusion. Box/cell representations of congruence families have a substantial earlier literature. We claim the explicit two-profile reduction only for this project's specified rank-24 catalogue and make no historical priority claim for the underlying tree symmetries. [Berger, Felzenbaum and Fraenkel, *Lattice parallelotopes and disjoint covering systems*](https://www.sciencedirect.com/science/article/pii/0012365X87902081) · [Dai, Li, Li and Yi, §2](https://arxiv.org/html/2611.15110v1)

## Reproduction

From `Research/OperationSelfridge/Continuation`, both exact replays use only the Python standard library. The second reuses the independently written arithmetic verifier in `Review/check_original.py`.

```sh
python3 Dominance/verify_orbits.py
python3 Dominance/verify.py
```

The following commands recreate the heuristic runs in an empty output directory, leaving the reference archives intact. They need NumPy and python-sat with CaDiCaL 1.9.5. The supplied verifiers check the committed evidence independently of reproducibility of solver tie-breaking.

```sh
mkdir -p /tmp/selfridge-r24
python3 Dominance/repair.py --output /tmp/selfridge-r24/repairs.json.gz
python3 Dominance/search.py --repairs /tmp/selfridge-r24/repairs.json.gz --output /tmp/selfridge-r24/search.json.gz --rounds 8
python3 Dominance/search.py --repairs /tmp/selfridge-r24/repairs.json.gz --extra /tmp/selfridge-r24/search.json.gz --output /tmp/selfridge-r24/challenger.json.gz --sample 65536 --sweeps 4 --sat-period 0 --rounds 6
python3 Dominance/search.py --repairs /tmp/selfridge-r24/repairs.json.gz --extra /tmp/selfridge-r24/challenger.json.gz --output /tmp/selfridge-r24/sibling.json.gz --orbit sibling --sample 65536 --sweeps 4 --sat-period 0 --rounds 6
python3 Dominance/grade.py
```

To continue the full-bank sibling search, copy `Dominance/sibling.json.gz` to a new path and give that path to `Dominance/search.py --output PATH --rounds N`. An existing output restores its saved phase assignment, cumulative observations, learned products and parameters. See the independent review for the Lean checks of generic set replacement and exclusion of a single forbidden value. The two-orbit classification has a written proof and an exhaustive Python replay. The catalogue-wide SAT models, arithmetic verifiers and heuristics are outside Lean.
