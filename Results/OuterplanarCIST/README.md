# Araki’s higher-outerplanarity obstruction conjecture is true

For every integer $k\ge4$, there is a 3-connected triangulated disc with a $k$-outerplanar embedding and no pair of completely independent spanning trees. This proves Conjecture 6.2 of [Toru Araki’s 2026 preprint](https://arxiv.org/pdf/2606.12827v1), p. 12. Araki’s definition asks for an embedding that peels in $k$ rounds. The minimum over all embeddings is a separate parameter.

## Construction and embedding

Start with the 25-vertex dual of the Tutte graph. Insert one vertex $p_f$ in every triangular face $f$ and join it to the three corners of that face, as in Araki’s construction. In the labeling in [Proof.lean](Proof.lean), choose the outer face with corners $0,1,p_0$, where core face 0 is $(0,1,2)$. This base graph has 71 vertices.

Add $k-4$ concentric triangles outside this outer face. Between successive triangles $A_0A_1A_2$ and $B_0B_1B_2$, add edges $B_iA_i,B_iA_{i+1}$, with subscripts modulo three. Each band of the resulting embedding consists of six triangular faces. The new outer face is the outermost triangle. The resulting graph has (71+3$k-4$) vertices.

The [embedding checker](verify_embedding.py) uses the same face list and core adjacency masks as the Lean file. It verifies that the base oriented triangles glue to a connected closed orientable surface, with one cyclic link at every vertex and Euler characteristic $71-207+138=2$, hence a sphere. Removing the chosen outer face gives the plane embedding. It also checks that deleting any two base vertices leaves the graph connected.

In a plane triangulation, once a connected set containing the outer-face boundary is deleted, the vertices on the new outer face are exactly the remaining vertices adjacent to the deleted set. All faces incident to deleted vertices merge with the outside. Every such face was triangular, so any surviving corner in the merged face had a deleted neighbor. The next deleted layer is therefore the next graph-distance layer. The base layer sizes are (3,32,33,3), and each new outer triangle adds one peeling round.

Deleting at most two vertices from an added band leaves part of each triangle. At least one of the three pairwise disjoint edges (B_iA_i) survives, and the surviving vertices of either triangle remain connected. Induction from the base graph proves 3-connectivity at every depth.

## Obstruction to two completely independent spanning trees

Araki’s Theorem 2.2 implies that two completely independent spanning trees give a partition into connected dominating sets. Indeed, the cross-edge graph of a CIST partition has no tree component and thus no isolated vertex. Color the two parts red and blue.

For a core triangle (f), call the vertices inserted into that face its interior. The outer annuli belong to the interior of core triangle 0 on the sphere. An interior vertex has neighbors only in its own interior or on its three corners.

Suppose a core triangle has only red corners. If its interior has a blue vertex, blue connectivity forces all blue vertices to stay in that interior. The stellar vertex of any other core face then has no blue neighbor, violating domination. If the interior has no blue vertex, its own stellar vertex has no blue neighbor. The same argument applies to blue corners. Thus every core triangle contains both colors.

Project each interior vertex to a corner of its own color. A same-color edge projects to a core edge or to a single vertex, since the three corners of each face form a clique. Therefore each color is still connected in the core.

The edges between the two colors now form a bond in the core, since they separate two connected induced subgraphs. A bond in a plane graph gives a cycle in its dual. Every triangle is mixed, so every dual vertex is on that cycle. This would give a Hamiltonian cycle of the Tutte graph, which has none. [Bondy and Murty, *Graph Theory*](https://www.zib.de/groetschel/teaching/WS1314/BondyMurtyGTWA.pdf)

The finite certificate in Lean independently rules out the same bipartitions of the core. It checks the boundary of each listed cut and exhausts the colorings in which every face has both colors. The Lean theorem applies for every number of annuli.

Lean checks the obstruction and its preservation for all members of the family. The planar embedding and the exact peeling depth follow from the oriented-face certificate and the geometric argument above.

## Source status and replay

On November 26, 2026, the [original preprint](https://arxiv.org/abs/2606.12827) still presented this as Conjecture 6.2. The [MathDB entry](https://mathdb.com/p/375262/the-higher-outerplanarity-obstruction-conjecture-for-complet) also had no posted solution. Searches by title, author, conjecture number, and construction found no earlier public resolution. The base graph is the obstruction credited to Péterfalvi and used by Araki. The extension to every depth is the result here.

Run `bash Results/OuterplanarCIST/verify.sh` with Lean 4.36.0 and Python 3. The optional argument is a mathlib checkout at `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. [Verification transcript](VERIFICATION.txt)
