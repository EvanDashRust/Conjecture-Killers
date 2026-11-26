# Graffiti.pc Conjecture 321 is true

Ermelinda DeLaViña announced this conjecture on March 4, 2007. The live *Written on the Wall II* catalog still marked it open when checked on November 25, 2026. [Opus 5's earlier public proof](https://gitlab.com/ai-village-agents/village/graffiti-verification/-/blob/6d9cf2ed6aefc02062d1615d95c876a0b72923b4/README.md#L22596) was published by August 21, 2026. It reduces the conjecture to at most seven vertices and checks the remaining cases. The independent Lean proof below gives the six-vertex bound directly. [University catalog](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) · [Catalog data](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json)

Let $G$ be a finite simple connected graph on $n>1$ vertices. Write $T(v)=\sum_w d(v,w)$ for the total distance from $v$, $T_{\max}=\max_v T(v)$, and $E_{\mathrm{avg}}$ for the average eccentricity. The original conjecture says that if $E_{\mathrm{avg}}\ge T_{\max}/3$, every inclusion-minimal total dominating set has minimum cardinality.

## Proof

Let $D>0$ be the diameter and take vertices $a,b$ at distance $D$. The triangle inequality gives $D\le d(a,v)+d(b,v)$ for every $v$. Summing,

$$
nD\le T(a)+T(b)\le 2T_{\max}
\le 6E_{\mathrm{avg}}\le 6D.
$$

Therefore $n\le 6$. At order six the chain forces every vertex to have eccentricity $D$. For $D\le 2$, the hypothesis also gives $T_{\max}\le 6$, so each vertex has at most one nonneighbor other than itself. For $D\ge 3$, every vertex has another vertex with neither an edge nor a common neighbor between them. Lean uses these necessary conditions to screen six-vertex graphs before computing full distances.

The Lean census covers all 33,866 labeled simple graphs of orders two through six. It enumerates subsets of the strict upper triangle of the adjacency matrix, uses breadth-first search to compute distances, and retains connected graphs satisfying the exact integer inequality $nT_{\max}\le 3\sum_v \mathrm{ecc}(v)$. For each qualifying graph it checks that the cardinalities of inclusion-minimal total dominating sets form a set of size at most one. The independent census found 245 qualifying labeled graphs.

## Lean replay

[Proof.lean](Proof.lean) states the original real-valued hypothesis with DeepMind’s `averageEccentricity` and `IsWellTotallyDominated` definitions. Lean proves the reduction to six vertices, validates the distance computations against the graph metric, and proves that relabeling preserves the quantities and minimal sets. The finite census uses kernel reduction through order four and Lean’s compiled `native_decide` for orders five and six.

With Git and Lean 4.33.1 available, run

```bash
bash Results/Graffiti321/verify.sh
```

The script pins the upstream *Formal Conjectures* revision, builds the imported modules, and checks the proof. It also accepts the path of an existing checkout at that revision. The final line reports the axioms of `Graffiti321.conjecture321`.
