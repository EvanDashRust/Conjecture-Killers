# Graffiti.pc Conjecture 138 is false

Conjecture 138 asserts that a finite simple connected graph $G$ satisfies

\[
\operatorname{path}(G)\ \ge\ (2+u(G))\operatorname{dist}_{\min}(M(G^2)).
\]

Here $\operatorname{path}(G)$ is the largest order of an induced path, $u(G)$ is 1 when the maximum independent set is unique and 0 otherwise, and $M(G^2)$ is the set of maximum-degree vertices of the square. The distance is the minimum distance in the square between distinct members of that set.

Ermelinda DeLaViña’s live *Written on the Wall II* catalog dates the conjecture to July 12, 2005. On November 25, 2026, the live entry marked it open and its comments contained only the announcement date. Searches of the literature, public counterexample trackers, and the Formal Conjectures repository found no earlier resolution. Enter `138` in the catalog’s search box to see the entry. [Live catalog](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html)

## Counterexamples

Take a path $p_0,p_1,\ldots,p_{2m}$ and attach two new leaves to each endpoint, with $m\ge7$. The result is a tree on $2m+5$ vertices.

- **Unique maximum independent set.** A maximum independent set includes both leaves at each end. If an endpoint of the original path belongs to the set, replacing it by its two leaves increases the size. With both endpoints excluded, omitting any leaf also fails maximality. The remaining path has vertices $p_1,\ldots,p_{2m-1}$. An independent set in it has size at most $m$, and size $m$ forces the indices $1,3,\ldots,2m-1$ by the gaps of at least two between selected indices. Thus $u(G)=1$.
- **Maximum-degree vertices of the square.** Each of $p_1$ and $p_{2m-1}$ sees three other original path vertices and two leaves within distance two. Every other vertex sees at most four others. These two vertices are therefore the entire set $M(G^2)$. Their distance in $G$ is $2m-2$, so in the square it is $m-1$. Each square edge represents at most two steps in $G$, and advancing two positions at a time attains that lower bound.
- **Longest induced path.** A path from a leaf at one end to a leaf at the other contains all $2m+1$ original path vertices and two leaves. Every simple path contains at most two leaves, giving $\operatorname{path}(G)=2m+3$.

The conjecture requires $2m+3\ge3(m-1)$, which fails for every $m\ge7$. The case $m=7$ has 19 vertices and gives $17<18$.

## Lean verification

`Graffiti138.conjecture138_false` uses the 19-vertex tree. It checks the exact maximum-degree pair and its square distance, the unique maximum independent set, and the exact longest induced path order. Lean proves that the finite checkers cover every independent set and every simple path of the required length, and checks their results with kernel reduction. The proof of the family above is given in prose.

```sh
bash Results/Graffiti138/verify.sh
```

The script uses Lean 4.36.0 and the finite graph definitions from the Conjecture 255 case. The main theorem depends on `propext`, `Classical.choice`, and `Quot.sound`.

[Lean source](Counterexample.lean)
