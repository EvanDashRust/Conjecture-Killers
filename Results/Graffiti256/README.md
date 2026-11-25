# Graffiti.pc Conjecture 256 is false

Let $A$ be the vertices of minimum degree in a finite simple connected graph $G$ with an edge. Conjecture 256 predicts

\[
\gamma_t(G)\max_{uv\in E(G)}|N(u)\cup N(v)|\ \ge\ 2|N(A)|.
\]

Here $\gamma_t(G)$ is the minimum size of a set containing a neighbor of every vertex. The catalog defines $N(A)$ as the union of the open neighborhoods of the vertices in $A$. Thus a member of $A$ belongs to $N(A)$ whenever it has a neighbor in $A$. DeLaViña’s *Written on the Wall II* dates the conjecture to February 23, 2007. The live entry credits Tony Newton with a 14-vertex counterexample submitted November 21, 2026. The 15-vertex construction below was found independently and is verified in Lean. Search for `256` in the catalog and open **Comments** to see the attribution and Newton’s graph. [Live catalog](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html)

## Counterexample

Join two vertices $p,q$ by one path $p-r-q$ of length two and by $k\ge6$ paths $p-x_i-y_i-q$ of length three. All the paths have distinct internal vertices, and these are all the edges. The graph has $2k+3$ vertices.

- The hubs $p,q$ have degree $k+1$. Every internal vertex has degree two, so these form $A$. The middle vertex $r$ is adjacent only to the hubs. Each $x_i,y_i$ is adjacent to its partner in $A$, and both hubs have neighbors in $A$. Therefore $N(A)=V(G)\setminus\{r\}$ and $|N(A)|=2k+2$.
- The union of the two open neighborhoods on a hub edge has size $k+3$. The hub has $k+1$ neighbors and the vertex at the other end has two, neither of which is a neighbor of the hub. On an edge $x_i y_i$ the union has size four. Therefore the maximum over edges is $k+3$.
- The set $\{p,r,q\}$ totally dominates the graph. A set of two vertices can only totally dominate if its two vertices are adjacent, and an edge neighborhood contains at most $k+3<2k+3$ vertices. A single vertex cannot dominate itself. Thus $\gamma_t(G)=3$.

The conjecture would require $3(k+3)\ge 2(2k+2)$. This fails for every $k\ge6$. Taking $k=6$ gives the 15-vertex Lean witness and the contradiction $27<28$.

## Lean verification

`Graffiti256.conjecture256_false` negates the inequality by applying it to the witness. Lean checks connectedness, the minimum-degree vertex set, the cardinality of its neighborhood, total domination, and the upper bound for every edge. The finite checks use `decide` in the Lean kernel. The script first builds the finite graph definitions from the Conjecture 255 result.

```sh
bash Results/Graffiti256/verify.sh
```

Lean 4.36.0 reports `[propext, Classical.choice, Quot.sound]` for the main theorem.

[Lean source](Counterexample.lean)
