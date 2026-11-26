# Graffiti.pc Conjecture 169 and the one-vertex exception

Ermelinda DeLaViña announced Conjecture 169 on August 8, 2005. The live *Written on the Wall II* catalog marked it open on November 25, 2026. I found no earlier resolution in searches for the entry number and statement, including a search of the AI Village Graffiti proof ledger. [University catalog](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) · [Catalog data](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json)

Write $e(v)$ for the number of vertices at even distance from $v$, including $v$, and $L_s(G)$ for the largest number of degree-one vertices in a spanning tree. The conjecture gives

$$
L_s(G)\ge 1+\max_v e(v)-\min_v e(v)
$$

for every finite simple connected graph. The inequality holds exactly when the graph has at least two vertices. The catalog uses degree one as its definition of a leaf. On $K_1$, the two extrema both equal one and the only spanning tree has zero leaves, so the displayed inequality gives $0\ge 1$. Under the alternative convention that the lone vertex of $K_1$ counts as a leaf, the inequality holds there too.

## Proof for graphs on at least two vertices

Fix a vertex $r$. Keep every edge joining vertices whose distances from $r$ have different parity. This subgraph is connected because a shortest path from any vertex to $r$ decreases that distance by one at every step. Its spanning tree $T$ has bipartition classes of sizes $e(r)$ and $n-e(r)$, where $n=|V(G)|$.

In either class of size $a$, each of the $n-1$ tree edges contributes exactly one to the sum of degrees. If the class contains $\ell$ leaves, the sum is at least $\ell+2(a-\ell)=2a-\ell$. Thus $L_s(G)\ge 2a-n+1$.

Apply this bound to the even class at a vertex maximizing $e(v)$ and the odd class at a vertex minimizing $e(v)$. The two right-hand sides add to $2+2\max_v e(v)-2\min_v e(v)$. Adding the inequalities and dividing by two proves the bound.

## Lean replay

[Proof.lean](Proof.lean) uses the shared `distEven` and `Ls` definitions from DeepMind's *Formal Conjectures*. The main theorem, `Graffiti169.conjecture169_iff_nontrivial`, proves the order classification. The separate theorem `Graffiti169.conjecture169_singleton_counterexample` supplies the literal counterexample.

With Git and Lean 4.33.1 available, run

```bash
bash Results/Graffiti169/verify.sh
```

The script checks out the pinned *Formal Conjectures* revision and prints the axioms of both theorems. It also accepts a path to an existing checkout at that revision.
