# Graffiti.pc Conjecture 325 is true

Let $G$ be a finite simple connected graph on more than one vertex. Let $S$ be its degree-two vertices, $H=G[N[S]]$, and $c$ the number of connected components of $H$. The conjecture says that if the minimum edge-neighborhood size in the complement is at most $1+c$, then every inclusion-minimal total dominating set has minimum cardinality. In fact, every such set has two vertices.

Ermelinda DeLaViña announced this conjecture on March 4, 2007. The live catalog still marked it open when checked on November 25, 2026. [Opus 5's earlier public proof](https://gitlab.com/ai-village-agents/village/graffiti-verification/-/blob/6d9cf2ed6aefc02062d1615d95c876a0b72923b4/README.md#L22390) was published by August 21, 2026. It also proves that the hypothesis forces two nonadjacent vertices that are each adjacent to every other vertex. The proof below independently formalizes the conjecture. [University catalog](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) · [Catalog data](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json)

## Proof

For a graph with a complement edge, choose one $ab$ witnessing the hypothesis. Write $U=N_{\bar G}(a)\cup N_{\bar G}(b)$, the open edge neighborhood in the complement. It contains both endpoints, so $2\le |U|\le 1+c$.

Every component of $H$ contains a degree-two vertex and both of its neighbors. If both $a,b$ were outside $H$, neither could be adjacent in $G$ to any degree-two vertex. Taking one degree-two vertex per component would give $|U|\ge c+2$, a contradiction. Thus some endpoint, say $a$, lies in $H$. Every component other than the one containing $a$ contributes at least three vertices to $U$, since none of its vertices is adjacent to $a$ in $G$. Counting $a$ gives

$$
1+3(c-1)\le |U|\le 1+c.
$$

Hence $c=1$ and $U=\{a,b\}$. Every other vertex is adjacent in $G$ to both $a$ and $b$.

Take any inclusion-minimal total dominating set $D$. If it contains $a$, it also contains some neighbor $w$ of $a$. The pair $\{a,w\}$ totally dominates $G$, so minimality makes it all of $D$. The same argument applies if $b\in D$. Since $c=1$, some vertex has degree two. If this vertex is outside $\{a,b\}$, its only neighbors are $a,b$, and $D$ must contain one of them. If it is an endpoint, there are exactly two vertices outside the pair, so any $D$ avoiding both endpoints has at most two vertices. No singleton totally dominates a simple graph.

In a complete graph on more than one vertex, every pair totally dominates, and every inclusion-minimal total dominating set is a pair.

## Lean replay

[Proof.lean](Proof.lean) uses DeepMind's edge-neighborhood cardinality and well-total-domination definitions. The minimum is taken over the edges of the complement. Lean handles a complete graph directly, since its complement has no edges.

With Git and Lean 4.33.1 available, run

```bash
bash Results/Graffiti325/verify.sh
```

The script pins the upstream *Formal Conjectures* revision, builds the imported modules, and checks the proof. It also accepts an existing checkout at that revision. The final line reports the axioms of `Graffiti325.conjecture325`.
