# Ten conjectures from Written on the Wall II

Nine proofs and one counterexample. Every row is a separate statement in Ermelinda DeLaViña’s catalog. The verdicts below use the catalog’s definitions and scope.

| Graffiti.pc | Verdict | Lean source | Argument |
|---|---|---|---|
| 161 | True | [SpanningLeaves.lean](SpanningLeaves.lean) | Every nonempty proper clique in a connected graph has a vertex incident with an edge leaving the clique. The degree of that vertex bounds the clique size. A spanning tree can retain all its incident edges, and the tree’s degree sum bounds that degree by the leaf count. |
| 162 | True for positive minimum degree | [SpanningLeaves.lean](SpanningLeaves.lean) | If the minimum degree is at least two, the floor factor vanishes. Otherwise the minimum local independence is one. Keep edges between nonsimplicial vertices and attach each simplicial vertex by a single edge to that connected subgraph. Handle the two-vertex graph directly. |
| 271 | True | [MaximumDegreeDistance.lean](MaximumDegreeDistance.lean) | Each distance level along a geodesic requires two selected vertices within two levels. Bands spaced five levels apart are disjoint. The cases with two, three, or four selected vertices give the required sharper bounds. |
| 310 | True | [TotalDistance.lean](TotalDistance.lean) | From a vertex of minimum transmission, select the root and the shortest-path predecessors of all vertices at distance at least two. Charge each distinct predecessor at least three units of transmission using a distinct child and, when needed, the predecessor itself. A universal root uses a pair. |
| 393a | True | [MatchingBound.lean](MatchingBound.lean) | Match supports lying in the second open neighborhood to distinct leaves. In the residual induced graph, orient a maximum matching so that its selected endpoints dominate every nonisolated vertex. An edge replacement rules out conflicting choices. |
| 393b | True | [TwoDomination.lean](TwoDomination.lean) | Each support that still has to be added has at least two support neighbors. The degree sum in the support-induced graph bounds the number of such supports by its edge count. |
| 393c | True | [TwoDomination.lean](TwoDomination.lean) | Select the vertices outside the second open neighborhood, the supports, and the vertices with exactly one neighbor in the closed neighborhood of the leaves. Every omitted vertex has at least two support neighbors. |
| 393d | False | [CoronaCounterexample.lean](CoronaCounterexample.lean) | A connected 42-vertex corona has 2-domination number 26 and a right-hand side of 25. |
| 416 | True, even without subtracting two | [Critical.lean](Critical.lean) | With a leaf and diameter at most two, every leaf shares a universal neighbor. The isolates in the second open neighborhood are leaves. A maximum critical independent set contains every leaf by the signed critical-difference argument. |
| 432b | True | [IndependentDomination.lean](IndependentDomination.lean) | For a nonbipartite graph, extend the leaves to an independent dominating set. For a bipartite graph, the smaller parity class independently dominates. There are at most as many supports as vertices in that class, by matching supports in the other class to distinct leaves. |

## Source conventions

For #161, the local independence number is taken **in the complement**, following the overline in the source HTML. For #162, the single-vertex graph has minimum degree zero, so the printed quotient is undefined there. The Lean theorem includes every connected graph on which that quotient is defined. For #271, the squared bound is equivalent to the ceiling of the square root. The result applies whenever the total domination number is defined. For #310, the sum includes the root’s zero distance, and integer ceiling division is applied before comparing cardinalities.

For #393a–d, each nested neighborhood is a composition of two **open** neighborhoods. The set in the “exactly one neighbor” term of #393c is the **closed** neighborhood of the leaves. #393a supplies an actual matching, which has size at most the matching number in the source. For #416, critical difference is a signed integer and the last maximization is by cardinality among the critical independent sets. For #432b, the difference between even and odd distance counts is signed and the root contributes to the even count. The Lean witness works against every root, hence against the minimum.

## The counterexample to 393d

Use a core on vertices 0 through 20. Vertices 0 through 3 form a clique. Vertices 4 through 20 form the square of a cycle in that order, with edges `4–6` and `5–7` removed. Add edges `0–4`, `1–5`, `2–6`, and `3–7`. Attach a private leaf to each core vertex.

The core is 4-regular and has exactly one 4-clique. In the full graph, the 21 core vertices are exactly the maximum-degree vertices and exactly the open neighborhood of the leaves. Their open neighborhood is the whole graph. The matching term is zero, the independence term counts all 21 leaves, and four vertices tie for the maximum incident 4-clique count.

Every 2-dominating set contains all 21 leaves. Its selected core vertices must dominate the core, since an unselected core vertex can take at most one neighbor from the leaf set. Each selected core vertex covers at most five core vertices, so at least five are needed. Adding core vertices 0, 1, 8, 13, and 18 to the leaves achieves 26. The finite checks in Lean use kernel reduction.

## Status and priority

On November 26, 2026, the live [Written on the Wall II catalog](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) listed each row as open, with no recorded result in its [comments](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/comments.json). The corresponding [statement data](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json) and [definitions](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json) were checked directly.

The search for earlier resolutions covered [the Graffiti verification ledger](https://gitlab.com/ai-village-agents/village/graffiti-verification/-/blob/8bd9f691fd56a2ba070ba3b6c8750ad6d71/README.md), [the WoW and West dossier](https://gist.github.com/siddhantdubey/22f22a7a23db5174ee59e32eaa8724aa/fdb1276794056c8af4a3ba730383f7e9629bb87c), [Formal Conjectures issues](https://github.com/google-deepmind/formal-conjectures/issues?q=is%3Aissue+WrittenOnTheWallII), and searches of the mathematical literature. This surfaced earlier resolutions of other catalog-open rows, including #398 and #422b. No earlier resolution of these ten exact rows turned up in that search. This is a public-record finding. The #161 proof uses standard spanning-tree facts and #416 uses the pendant property of maximum critical independent sets already recorded by [Craig E. Larson](https://independencenumber.wordpress.com/wp-content/uploads/2012/07/inp-alpha-properties-120803.pdf). Douglas West [also lists #161](https://dwest.web.illinois.edu/regs/graffiti.html).

The catalog data SHA-256 hashes at inspection were:

| File | SHA-256 |
|---|---|
| `conjectures.json` | `be996f263ee2d6ae077fd3e9a3e7f79a824e1be160ee284e5f3b7dd7151aaadb` |
| `definitions.json` | `3939e996f49620ca3a59244f503f921a70fcfd297008afbf682c440b85ce2418` |
| `comments.json` | `0f4e5791055f2a3c715879509aa2a74368850eea92cbb852f5e628163e36336c` |

## Replay

Use Lean 4.36.0. The script pins mathlib to `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` and accepts an existing checkout of that commit as its optional argument.

```bash
bash Results/GraffitiBatch/verify.sh
```

[Verification output](VERIFICATION.txt)
