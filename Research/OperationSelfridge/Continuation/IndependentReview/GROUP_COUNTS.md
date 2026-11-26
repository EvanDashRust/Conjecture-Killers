# At least twenty moduli divisible by 7 or 11

Every finite covering by congruence classes with distinct odd numerical moduli greater than one has at least **20** moduli divisible by 7 or 11, counting their union once. In the absence of 11 from the period, at least 20 moduli are divisible by 7. In the absence of 7, at least **58** are divisible by 11 and **45** by 13. These improve the initial pair estimates in [COMMON_HOLE.md](COMMON_HOLE.md), which supplies additional counts for 17, 19, 23, 29 and 31.

## Grouped projection on a common residual set

Use the residual measure μ and its missed set H of measure strictly larger than h as in the preceding note. In the 7- or 11-only restoration, delete all classes divisible by 7 or 11, and take h=181617/1000000. In the 13 restoration, 7 is absent and h=119046/1000000. A restored label has form $p^a d$ with d coprime to p. After fixing the other suppressed coordinate at an untouched root, or when no other coordinate is being restored, all p-fibres of H must be covered. Thus the sum of the normalized contributions is at least p, where a normalized contribution is $p^{1-a}$ times the relative H-mass of the cofactor class modulo d.

Choose 16 particular cofactors from the first-power labels, listed in the checker. Let J be the subset whose labels are actually present. Write $N_J$ for the number of their projected classes matching the remaining coordinates. For each nonnegative integer t,
$$
  \mathbb E_{\mu\mid H} N_J \le t + \frac1h\mathbb E_{\mu}(N_J-t)_+.
$$
In the last expectation, μ is the original residual measure with the published conditional coordinate caps. Apply Dai–Li–Li–Yi Theorem 2.6 with the increasing convex hinge. This bounds the rightmost expectation by the one for
$$Y_J=\sum_{d\in J}1_{d\mid R},$$
where the independent exponents of R have tails $\gamma_q/q^e$ for the corresponding prime coordinates, with full unbounded comparison permitted. Any absent coordinates may be included in the upper comparison. The distinction between μ and its conditioning on H is essential.

For any subset $I\subseteq J$, independence gives
$$\mathbb E\prod_{d\in I}1_{d\mid R}=W(\operatorname{lcm}(I)),$$
with $W(1)=1$. Given t, expand the function $s\mapsto (s-t)_+$ on the integers 0 through 16 in the binomial basis. The checker tests the coefficient identity independently on every argument. The expected binomial moment of order j is the sum of the displayed intersections over all j-element subsets of J. Hence all hinge expectations for all $2^{16}$ subsets J are computed exactly by a finite subset sum. Take the minimum over integer thresholds t, then the maximum over J of each fixed size s. For the remaining k−s labels use the sum of the k−s largest single-label bounds from the preceding note, excluding exactly those 16 chosen numerical labels. This last list includes all higher powers of p. Numerical distinctness is the only restriction imposed on the choice of the remaining labels.

For the single-label ranking, $W(d)^4\le16/(3d^3)$ justifies the cutoff b=10000 on $b=p^{a-1}d$, checked against the k-th retained weight. All group and ranking operations use exact integer or rational arithmetic. The normalized sums obtained for (p,k)=(7,19),(11,57),(13,44) are strictly below 6.888, 10.965 and 12.940, respectively, each less than p.

## Both 7 and 11

Retain the [earlier notation](COMMON_HOLE.md) A,B,C for the numbers of labels involving just 7, just 11, or both of the distinguished primes. Assume $A+B+C\le19$. If any 11-root is untouched by the B and C labels, the A labels must restore all 7-fibres of H, requiring at least 20 by the grouped estimate. If any 7-root is untouched by the A and C labels, the B labels similarly need at least 58. Thus $A+C\ge7$ and $B+C\ge11$.

Let z,s be the numbers of 7-roots receiving exactly zero or one of the A labels; let u,t be the corresponding counts for the B labels on the 11-coordinate. Each of the $zu$ doubly empty cells needs a C label. If it receives exactly one then that label must involve only first powers of 7 and 11 and its projected cofactor class must contain H. For all such singly filled cells the cofactors are distinct by numerical distinctness. Their lcm D has $W(D)\ge h$, so $\tau(D)\le3$ by the finite fourth-power enumeration. Consequently the doubly empty cells need at least $2zu-\min(3,zu)$ mixed labels.

Of the s singly populated A-roots, at most three can restore H on their own without any B or C label at a cell. Each such A label would have first 7-exponent and cofactor containing the common H, giving the same divisor-count bound. Therefore the cells above the u empty B-roots and the remaining singly populated A-roots require at least $(s-3)_+u$ mixed labels. The transposed argument costs $z(t-3)_+$ more. The three counted sets of cells are disjoint and a single mixed label touches only one cell. Hence
$$
 C\ge 2zu-\min(3,zu)+(s-3)_+u+z(t-3)_+.
$$
The elementary bounds $s+2(7-z-s)\le A$, and equality $A=s$ when all seven roots have at most one A-label, hold, along with their transposes. Exhausting the finite integer possibilities leaves the following rows.

| A | B | C | z | s | u | t |
|---:|---:|---:|---:|---:|---:|---:|
| 7 | 11 | 0 | 0 | 7 | 0 | 11 |
| 7 | 11 | 1 | 0 | 7 | 0 | 11 |
| 7 | 12 | 0 | 0 | 7 | 0 | 10 |
| 8 | 11 | 0 | 0 | 6 | 0 | 11 |

In every row at least six 7-roots have a single A label. If one of these uses a higher power of 7, choose a full 7-coordinate in that root escaping it. Otherwise all six have first 7-exponent and their cofactors are distinct. Only five possible cofactors have $W(d)>1/9$, namely 1,3,5,9,15. Thus some such root admits A-coverage of at most 1/9 in μ-mass. Fix the chosen full 7-coordinate; the still-uncovered subset $H'\subseteq H$ has mass greater than $h-1/9$.

At most 12 B and C labels remain at that coordinate. They must hit all eleven 11-roots on $H'$, so at least ten roots have only a single restoring label. At most one of these can use a C label. The others give at least nine distinct B labels of first 11-exponent whose cofactor classes contain all of $H'$. Their cofactor lcm D must satisfy $\tau(D)\ge9$ and $W(D)>h-1/9$. The same finite enumeration gives $\tau(D)\le4$ for all such D. This contradiction proves the bound of 20.

## Replay

From the continuation directory run `python3 IndependentReview/group_counts.py`. [Exact transcript](group_counts.txt). The proof inherits the omitted-stage rational margins and the scalar comparison of Dai et al. No additional Lean statement certifies this grouped or joint-grid argument. A targeted literature search found no matching numerical result in the cited preprint or public problem history. Priority is provisional. [Dai–Li–Li–Yi](https://arxiv.org/html/2611.15110v1) · [Erdős problem history](https://www.erdosproblems.com/history/7).
