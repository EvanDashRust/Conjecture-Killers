# Graffiti.pc Conjecture 318 is true

Let $G$ be a finite simple connected graph with at least two vertices. Let $e(\overline G)$ be the number of edges of its complement, and let $d_{\rm even}(v)$ count the vertices at even distance from $v$, including $v$ itself. The conjecture says that if $\max_v d_{\rm even}(v)\ge e(\overline G)$, then every inclusion-minimal total dominating set has minimum cardinality. In fact, every such minimal set is a pair.

The current catalogue data classify the March 4, 2007 entry as open. I found no earlier resolution of this statement in searches through November 25, 2026. The earlier *Written on the Wall* series also has an item numbered 318, concerning maximum degree in triangle-free graphs. [Written on the Wall II catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html)

## Proof

Take a vertex $v$ with $e(\overline G)\le d_{\rm even}(v)$. Every other vertex at even distance from $v$ is a non-neighbor of $v$ in $G$, since adjacent vertices have distance one. Hence
$$
e(\overline G)\le d_{\rm even}(v)\le 1+\deg_{\overline G}(v).
$$
Therefore there is at most one edge of $\overline G$ with both endpoints outside $v$.

Let $D$ be any total dominating set and choose $a\in D$ adjacent to $v$.

- If $D$ contains a vertex $b\ne v$ adjacent to $a$, the pair $\{a,b\}$ dominates $v$ and each of its own vertices. A remaining vertex missed by both would give two distinct complement edges disjoint from $v$. Thus the pair totally dominates $G$.
- Otherwise the only possible neighbor of $a$ in $D$ is $v$, so $v\in D$. Suppose a vertex $x$ is missed by $\{a,v\}$ and choose its neighbor $b\in D$. The vertices $a,x,b$ are distinct and lie outside $v$. The pairs $ax$ and $ab$ are distinct complement edges, a contradiction. Hence $\{a,v\}$ totally dominates $G$.

Every total dominating set contains one of these pairs. A singleton cannot totally dominate a simple graph, since its only member needs a neighbor in the set. This proves the conjecture.

## Lean replay

[Proof.lean](Proof.lean) uses DeepMind’s existing definitions of even-distance counts, total domination, and well-total-domination from *Formal Conjectures*. This individual entry has no standalone statement in the pinned revision. The proof imports the shared definitions directly.

With Git and Lean 4.33.1 available, run the following from the repository root.

```bash
bash Results/Graffiti318/verify.sh
```

The script checks out the pinned version of *Formal Conjectures*, builds the two imported modules, and checks the proof. It also accepts the path of an existing checkout at the pinned revision. Lean prints the axioms of `Graffiti318.conjecture318`.
