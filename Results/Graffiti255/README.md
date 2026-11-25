# Graffiti.pc Conjecture 255 is false

Conjecture 255 predicts that every simple connected graph with an edge satisfies

\[
\gamma_t(G)\;\max_{uv\in E(G)} |N(u)\cup N(v)|\ \ge\ 2|C(G)|.
\]

Here $\gamma_t(G)$ is the minimum size of a set containing a neighbor of every vertex, $N(u)$ is the open neighborhood of $u$, and $C(G)$ is the set of vertices with minimum eccentricity. Ermelinda DeLaViña’s *Written on the Wall II* dates the conjecture to February 23, 2007 and still lists it as open in the catalog updated November 5, 2026. Literature and repository searches found no earlier resolution as of November 25, 2026. [Catalog, page 148](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf#page=148)

## Counterexample

Take a clique on $a_0,\ldots,a_4$. Add a hub $h$ and join each $a_i$ to $h$ by a two-edge path $a_i-b_i-h$, with a distinct new vertex $b_i$ on each path. These are all the edges.

- Every vertex has eccentricity 2. A clique vertex $a_i$ reaches each $b_j$ via $a_j$ when $j\ne i$. The vertices $b_i$ reach each other via $h$, and $h$ reaches each $a_i$ via $b_i$. Every vertex has a nonneighbor. Thus $|C(G)|=11$.
- Every edge has a neighborhood union of size 7. For $a_i a_j$ the union consists of the five clique vertices and $b_i,b_j$. For $a_i b_i$ it consists of the clique, $b_i$ and $h$. For $b_i h$ it consists of the five $b$ vertices, $a_i$ and $h$.
- The three vertices $a_0,b_0,h$ totally dominate the graph. A two-vertex total dominating set must be adjacent so its members can dominate each other, but every adjacent pair reaches only seven vertices in its open neighborhood union. Hence $\gamma_t(G)=3$.

The conjectured inequality therefore requires $3\cdot 7\ge 2\cdot 11$, which fails.

The same construction with a clique of size $m\ge5$ gives a family of counterexamples. The three invariants are $\gamma_t(G)=3$, $|C(G)|=2m+1$, and a neighborhood union of size $m+2$ for every edge.

## Lean verification

The Lean theorem `Graffiti255.conjecture255_false` negates the inequality by applying it to the 11-vertex graph and the three-vertex total dominating set. The file separately checks that the set has minimum size and that all edge neighborhood sizes are exactly seven. The finite checks use `decide` in the Lean kernel.

```sh
cd Results/Graffiti255
lean Counterexample.lean
```

Lean 4.36.0 reports `[propext, Classical.choice, Quot.sound]` for the main theorem.

[Lean source](Counterexample.lean)
