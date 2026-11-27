# Independent review of the two fibre counts

I reviewed commit 73fb39da9f6158f3d5dff6b154c2afb66f298a2e, the observed live head of the research branch at the start of this review. I found no mathematical or computational defect affecting the two published count bounds. The complete implications from a hypothetical covering to those counts remain written and computer-assisted proofs.

## Directed rounding and the infinite tail

I checked the conditional cylinder cap against Dai, Li, Li and Yi, Lemmas 2.1, 2.3 and Theorem 2.6, including the conditioning of the 3-coordinate in their Corollary 2.13. The nonnegative correction in the positive-part identity is the only term using truncated variables. Replacing multipliers by their minimum with 10 increases that correction. Discarding histogram products above every retained threshold is sound because later multipliers are at least one. Ceilings are applied separately to positive masses, their products and the analytic moment recurrences. Padding prime coordinates outside the period only increases the comparison variables. The cubic bound is homogeneous in the third moment. After the finite schedule changes, all subsequent moment multipliers match the baseline, justifying rescaling the analytic Section 4.3 tail bound by the ratio of exact moments.

The archived commands independently replayed the three guaranteed uncovered masses above 0.7494330758, 0.2097419703 and 0.2085117590, along with all seven conditional volume checks and the two five-adic certificates. The previous checker’s ternary threshold is 18 for its relaxation.

## A second, shorter computation for the ternary count

The additional independent C++ computation shows that with 17 tokens the path weight on some branch falls to at most 7283 in units of 1/10000, below the required 7494. Its state does not encode the multisets in the original Python procedure.

Compute the ordered upper palette independently by factoring all eligible cofactors below 4096. Each missing weight is at most the reciprocal square root of the cofactor, below the 18th retained weight. The pure-power class is charged 7494 units. For each token budget, compute the largest possible guaranteed path weight in a relaxation with three children at every vertex and independent label supplies in subtrees. If a node uses $k$ labels on its immediate children, replace the labels by the top $k$ and try each allocation among the children. Partition the remaining budget among the three independent subtrees. A guaranteed bound for this allocation is the minimum of (child prefix weight plus child continuation bound). Maximize over allocations. The small budget tables are built in increasing order. An empty level with an entire budget placed in a single child gives minimum zero.

Compute a second table with the pure-power label forbidden on the immediate children, allowing the full first relaxation further down. Finally, at the tree's second global level, only one of the three first-digit subtrees can use a pure-power label. Use the unrestricted table in one subtree and the restricted table in the other two. These relaxations contain every actual arrangement. Pruning inside the maximum only discards a partial allocation when the remaining sum cannot improve the incumbent. The bounds for budgets 15, 16 and 17 are respectively 6767, 7035 and 7283. At later depths different parent nodes may freely reuse labels, so a solution to the relaxation need not realize any congruence family.

    python3 ternary_palette.py > palette.txt
    c++ -std=c++17 -O3 sibling_review.cpp -o sibling_review
    ./sibling_review < palette.txt

## Five-adic review

I checked the possible sorted five-row profiles, including the size-five profile at budget ten. Discarding higher 5-adic exponents in a short row is justified by fixing a single second digit which avoids all deeper classes in that row. It leaves the projected classes covering the same set of head holes on every row. The restrictions on numerical cofactor labels use distinctness only after this deletion. The two distorted measures have the same uncovered set, so their independent necessary conditions apply to the same choices of labels and phases.

I also reimplemented the critical simultaneous pair tests using actual residues on the full CRT grid. For each new class, the translations preserving all previously fixed phases shift the new phase by multiples of their lcm. Thus only gcd(previous lcm, new modulus) residues need inspection. The independent code explicitly evaluates the intersections of row unions, then computes their maximal allowed mass by sorting cell values within each conditional coordinate. It reproduced the exact rational outcomes for all 17 recorded critical cases, including the extra class modulo 9.

    python3 direct_crt_review.py

The reviewed proof uses exact Python for several finite comparisons and published analysis for the distortion principle. Lean checks arithmetic and counting components. The independent checks here do not supply a Lean formalization of the complete bounds.

## Scope and attribution

The source is [Dai, Li, Li and Yi](https://arxiv.org/abs/2611.15110). The original certificate is the Conjecture Killers continuation. The independent palette, tree dynamic program and direct CRT-grid check accompany this review. The new joint-obstruction argument is recorded separately.
