# Type 3 covers exist at every width from 19 onward

Paul R. Emanuel asked whether Type 3 two-row incongruent restricted disjoint covering systems exist at every sufficiently large width. Under the coefficient convention used in his worked examples and horizontal doubling, the answer is **yes** for every \(n\ge19\), with both rows near IRDCS. I found no prior resolution in searches on November 25, 2026. [Emanuel, *Covering systems*, Definition 7.9 and §7.4.1](https://doi.org/10.25949/19441907)

Definition 7.2 prints \(1<a,b<m\). The Lean theorem uses \(1\le a,b<m\). The induction introduces modulus 2, for which the printed strict inequalities have no integer solution. The construction therefore leaves open the existence question with the printed strict bound. [Source and formalization audit](TYPE_THREE_SOURCE_AUDIT.md)

## The induction

A row has a **near-cover witness** if some congruence hits it once, and there is a hole on either side of the row strictly before the next hit of that same congruence. Extending the interval in either direction far enough to give the singleton a second hit would include a hole. The Lean proof checks this implication directly.

Keep a two-row cover of width \(w\) with such a witness in each row. The induction also requires that the lower row can lose its last point while each modulus still hits both rows and has at least two hits in one row.

- To make width \(2w\), put the old lower row at even columns and the old upper row at odd columns. Double all old moduli and scale and translate their residues with their columns. Fill the complementary parity in each row with a single new congruence of modulus 2.
- To make width \(2w-1\), put the old lower row at odd columns and the old upper row at even columns. The lower row therefore contributes its shortened version. The same modulus-2 rule fills the complementary parity.

In both constructions the new lower row ends with a modulus-2 point and can lose it. The old singleton and its two holes are scaled together, so their order is preserved. Every congruence has a point in each row and at least two points in one row, which gives three noncollinear points.

Explicit seeds cover widths 19 through 36. Every width \(n\ge37\) is either \(2w\) or \(2w-1\) for a smaller \(w\ge19\). The bound 19 is sufficient for this construction. The linear congruence model allows coefficient 1, as Emanuel’s worked examples and his modulus-2 horizontal doubling do.

## Lean verification

Lean checks the seed data by reduction, the induction, and the realization by linear congruences on the two-row rectangle. The main theorem is `DisjointCovers.emanuel_type_three_from_nineteen`.

```sh
bash Results/DisjointCovers/verify.sh
```

- [Seed certificates, induction, and the obstruction to extending a near row](NearStrips.lean)
- [Realization as a two-dimensional IRDCS and the main theorem](TypeThree.lean)
