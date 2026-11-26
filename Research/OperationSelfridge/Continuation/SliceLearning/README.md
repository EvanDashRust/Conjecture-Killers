# How many phase changes can repair the released rank-24 layouts?

Fix the 24 primes and their heights in `Runs/released24.json.gz`. A slot specifies a nonempty set of coordinates and one of the allowed modes on each. A layout chooses at most one phase of each slot. An edit assigns a new phase to a previously absent slot or changes an existing phase. Deleting old patterns can only remove coverage and can be omitted when testing an upper budget. The bounds below permit edits to **any** such slot, including shapes absent from the released catalogue and arbitrary support sizes. They concern this fixed alphabet.

| Starting layout | Exact minimum number of supplementary phases if the old phases may all remain | Lower bound on edits when each slot may have only one phase | Disjoint certified escaping atom words |
|---|---:|---:|---:|
| Released latest, changing only the variable 3-phase 12 to 2 | 7 | 10 | 164859974858421502270823826432000 |
| Released latest after both stages of the dominance repair | 5 | 9 | 21475855258515684941885765222400 |
| Released scored incumbent after both stages of the dominance repair | 5 | 9 | 17863587575633862891394921267200 |

The supplementary phases must have distinct slots among themselves, but in that column a slot may retain its original phase alongside a new one. All three upper bounds use only the 3- and 5-coordinates. The checker tests their union with the retained head patterns on all 18 × 20 atom pairs. These are explicit covers of that relaxed problem. The repeated slots prevent their use as solutions of the distinct-mode problem. The edit lower bounds in the adjacent column respect replacement at every unary and pair slot.

## Certificate of the lower bounds

For each layout there are 512 labelled points outside the old union. Under the per-root CRT generator take the escaping integer congruent to $-1$ at every auxiliary prime and to $r+d p^h$ modulo $p^{h+1}$ for each coordinate atom $(r,d)$. This makes each first exit occur immediately at height $h$. An auxiliary prime $q$ assigned to any root exceeds $h+1$. Its selected residue $q-1$ would require agreement through $p^{q-1}$, impossible at a different low root or after this immediate exit. The certificate retains every original coordinate and the integer itself. Its further 1,024 test words per layout are covered by one or more old unary or pair phases and avoid all old higher-arity phases. They expose coverage lost by changing low-arity slots. They are not asserted to be original holes.

To exclude a budget, give the repair every unary and every pair slot at the indicated heights, at most once each. Allow all old phases of arity at least three to remain even when the corresponding slot would be changed. Replace each proposed change of arity at least three by the cylinder prescribing its shallow phase at any three of its coordinates, and allow these shallow triples unlimited repetitions. Every legal addition of arity at least three lies within such a triple: for positive height a fixed higher digit cylinder and a variable atom both prescribe the shallow residue; at height zero the sole mode is already shallow. The relaxed family therefore covers at least as much as the legal repair it represents.

For any partial assignment and each witness, record every old unary or pair slot that hits it. A witness becomes active if all those slots have been changed and none of the assigned new phases yet hits it. Future changes can remove more original phases. Every currently active word must still be covered by a new phase. If `k > 0` changes remain and there are `n > 0` active words, at least one remaining phase in a completion must cover at least `ceil(n/k)` of them. The checker enumerates every available unary or pair phase and every repeatable shallow triple reaching this threshold. A coordinate value hitting fewer than the threshold can be skipped, since adding more coordinates cannot increase its point count. Recursing after each eligible change explores every possible completion up to ordering. The newly covered mask is calculated over **all** test words before rebuilding the active set. Thus the algorithm does not forget obligations when a formerly useful phase is removed. With zero changes and an active witness, the branch fails. With zero active words the finite test succeeds. Every branch fails at the tabulated excluded budgets. For the supplementary lower bounds, initialize without any original phases and use only the 512 original holes.

## A separate lower bound on mixed edits when every unary is free

For the 3-only correction and the repaired scored incumbent, **at least four mixed slots** must change even if every unary is freely reassigned. For the repaired latest layout, **at least six mixed slots** must change under the same allowance. New mixed phases may use any support on the same 24 coordinates, of any size at least two, even with repetitions. The calculations keep every original mixed phase for free. Thus they also apply to replacements which lose the original phase.

The three finite products in `mixed_products.json` avoid every original mixed phase. On each axis exhaust the effect of deleting an arbitrary phase of each unary mode. Count the minimum number of distinct surviving shallow phase values over these choices. At height zero, one unary deletes at most one of the axis atoms. At positive height the checker enumerates all distinct residual masks, with optional omission at each mode. Every axis retains at least two shallow values; in the repaired latest case all but the 3-axis retain at least three. For any fixed global unary assignment, choose one surviving representative of each remaining shallow phase on each axis, uniformly and independently. The resulting product law avoids every fixed mixed pattern and every assigned unary. A new mixed phase fixes at least two shallow values, so its mass is at most the reciprocal of the product of the two smallest axis counts. The union bound now gives the stated mixed edit requirements. The products were located by finite constraint search. Verification uses only their listed atom sets and integer counting.

```sh
python3 SliceLearning/mixed_budget.py
```

### Extension of the mixed bounds to more primes and higher modes

The **4/6/4 mixed-pattern bounds** continue to hold on any finite extension by further odd primes and arbitrary increases of the 24 original heights. This statement retains the old mixed predicates on the section specified below, permits every unary phase at every enlarged coordinate, and counts each additional mixed pattern once. It concerns the abstract prefix model. The total-edit bounds in the table above are proved at the archived heights only.

For an old coordinate of height $h$ enlarged to $H>h$, restrict to points with the immediate-exit residue $r+d p^h\bmod p^{h+1}$ for each permitted old atom $(r,d)$. On this section, the old fixed modes retain their usual residues and the old variable phase agrees with the corresponding fixed residue at depth $h+1$. Thus an unchanged old mixed predicate still misses the entire product. A reassigned fixed unary at depth $h+1$ removes at most its one corresponding old atom, just as the old variable unary could; phases with zero digit there remove no section point. After choosing any surviving old atom, distribute its further fixed digits and its final nonzero exit digit uniformly. The total conditional mass of all remaining deeper unaries, one per mode including the variable mode at $H+1$, is at most
$$
\sum_{j=1}^{H-h-1}p^{-j}+\frac{p^{-(H-h-1)}}{p-1}
=\frac1{p-1}<1 .
$$
Every such old atom therefore has a surviving extension. The old shallow phases on this section still agree with the new shallow phases up to relabelling, including the case $h=0$.

A fresh prime $q$ is at least 101 since the original catalogue already includes every odd prime through 97. At positive fresh height the first unary removes at most one root modulo $q$. In each other root the sum of all deeper unary masses is at most $1/(q-1)<1$ under the conditional uniform law, by the same identity. Thus at least $q-1$ shallow values survive. At fresh height zero at least $q-2$ of the nonzero-digit phases remain. These new axes do not lower either of the two smallest certified axis counts. Choosing one surviving extension per shallow phase on every axis proves the same bound for additional mixed phases of arbitrary enlarged depths and supports. This argument treats every extension needed for the selected product; it never identifies an old atom with a single arbitrary imported integer.

## Product learning and full-family semantics

A product consists of one explicit set of labelled atoms per coordinate. An old pattern intersects it exactly when every prescribed coordinate phase is realized on its corresponding axis. Starting with an escaped word, `PatternIndex.grow` expands one axis at a time to all atoms that keep the whole product disjoint from every old pattern. Expanding later axes can only shrink the list of legal additions to earlier ones. Each archived layout has nine disjoint products, with distinct singleton first coordinates; their sizes therefore add. The total is a count of atom words. It is not a count of congruence classes or a lower bound on the natural density of escaping integers with that denominator.

`slice_batch` emits distinct points of a certified product. Every emitted point is a valid necessary constraint on a future candidate. Bounded batches sample a family. To enforce an entire family, `PatternIndex.hole(box)` recursively intersects the masks of still-compatible patterns with each coordinate. It prunes a branch once a matching pattern has no remaining coordinate and returns a concrete missing word if any exists. It returns `None` precisely when the **union** covers the whole product; different points may use different patterns. Both operations retain the original prime columns, heights, roots and first nonzero digits. The certificates apply directly on this labelled alphabet. Translating one archived escaping integer after an alphabet change adds a single necessary word and does not transport the full product.

## Replay

Run from `Research/OperationSelfridge/Continuation`, with Python 3 and its standard library:

```sh
python3 SliceLearning/checkpoint.py
python3 SliceLearning/checkpoint.py --model single_3
python3 SliceLearning/checkpoint.py --build
```

The last command deterministically reconstructs the compressed archive from the released source and the recorded repairs, then verifies it. The input hash, pattern hashes, all word and integer witnesses, product axes and the supplementary upper certificates are in `rank24_products.json.gz`. Integer arithmetic supplies the proof bounds. This written argument and the Python certificates have no Lean formalization.
