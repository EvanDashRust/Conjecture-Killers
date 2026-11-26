# Four required fresh primes in a frozen prefix extension

Consider the exact old-only phases, unaries, heights and prime list in [prefix_candidate.json](prefix_candidate.json). An extension may add one pattern for every mode vector involving at least one new odd prime, with arbitrary phases, arbitrary support, and arbitrary finite prefix heights on the new primes. A complete extension must have at least four fresh primes. In increasing order their first four values must satisfy

$$q_1<1100,\qquad q_2<1600,\qquad q_3<3200,\qquad q_4<500000.$$

There is no upper bound on the total number of new primes in this theorem. Old-only additions, changes to old phases, and changes to old heights are outside its scope. The conclusion concerns the prefix construction. The general equivalence with odd coverings does not require their old phases to match this layout.

## The old hole measure

Use the rational probability measure $\mu$ supported on holes of the archived core, constructed from the certified products in [the first-moment proof](CUMULATIVE_SEARCH.md). Let $a_v$ bound $\sup_\phi\mu(v=\phi)$ for one old mode vector $v$, including the empty vector. The sums needed here are
$$T=\sum_v a_v<27.095,\qquad
U=\sum_{v,w}a_{v\vee w}<3885.371.$$
Two phases on the same coordinate are nested or disjoint, since each variable mode specifies the whole low root and exit digit. Thus an intersection has mass at most the bound for the coordinatewise stronger mode $v\vee w$. At a single coordinate there are $2e+1$ ordered mode pairs with maximum $e$, counting 0 as the free mode. On the 17 height-zero tail coordinates this gives a weight of $3^{|S|}$ for the union support $S$. Multiplying these weights into the same exact head and mask-product sums gives $U$ in the verifier.

## Distorting only the large fresh coordinates

Call the new primes below a cutoff $K$ exceptional and let their set be $J$. Sample their full atom alphabets independently and uniformly. The mass of all added patterns supported on old and exceptional coordinates is at most
$$H=T\left(\prod_{p\in J}p/(p-1)-1\right).$$
This uses the fact that the uniform single-phase capacities of the nonfree modes at $p$ sum to $1/(p-1)$ for any height.

Process the other new primes in increasing order. At a prime $q$, on each fibre over the previous coordinates, let $\alpha$ be the uniform local probability of the patterns whose last prime is $q$. If $\alpha\le\delta$, put all mass uniformly on the good atoms. If $\alpha>\delta$, assign the good atoms density $\gamma=1/(1-\delta)$ relative to uniform and distribute the remaining mass uniformly over bad atoms. This preserves the earlier marginal and bounds every new conditional density by $\gamma$. The remaining bad mass is at most $(\alpha-\delta)_+/(1-\delta)\le\alpha^2/[4\delta(1-\delta)]$ pointwise.

Before reweighting at $q$, upper-bound $\alpha$ by the sum over new patterns of their $q$-phase capacities times the indicators of their earlier projections. Expand the square. Distinct mode vectors ensure at most one term per choice of earlier modes and last mode. Summing the products of last-mode capacities gives $1/(q-1)^2$. For a previous prime $p$, each intersection involving nonfree modes has conditional probability at most $\gamma$ times the uniform capacity of its strongest mode. Iterated conditioning works even when the different reweighted coordinates are dependent. At exceptional coordinates take $\gamma=1$. At height $h$, the ordered-pair sum over nonfree maxima is bounded by
$$\sum_{e=1}^h(2e+1)p^{-e}+(2h+3)\frac{p^{-h}}{p-1}
\le \sum_{e\ge1}(2e+1)p^{-e}=\frac{3p-1}{(p-1)^2}.$$
The inequality replaces the last term by an infinite series with larger coefficients. With $b_p=(3p-1)/(p-1)^2$, the total bad mass is bounded by
$$H+\frac{U\prod_{p\in J}(1+b_p)}{4\delta(1-\delta)}
\sum_{q\ge K\ {\rm prime}}\frac{1}{(q-1)^2}
\prod_{K\le p<q\ {\rm prime}}(1+\gamma b_p).$$
We included every prime above the cutoff. This upper bound applies simultaneously to all finite prime sets. If it is below one, positive mass survives on the old holes, and the finite extended box has an uncovered word. This also gives an actual escaping integer for the specified nonterminal per-root lift.

## An elementary infinite tail

Let $N=2^k$. In a dyadic block $[n,2n)$ with $n\ge N$ a power of two, every prime in the block exceeds $n$ and divides the central binomial coefficient $\binom{2n}{n}<4^n$. Thus there are at most $2n/k$ such primes. The sum of $\gamma b_p$ over the block is at most $B=2\gamma(3+2/N)/k$. The block product is at most $e^B\le (1-B/8)^{-8}=R$. With $R<2$, the whole remaining sum is at most the incoming prefix product times
$$\frac{2R}{kN(1-R/2)}.$$
All finite updates use upward integer rounding with denominator $10^{14}$. The tail uses rational arithmetic. The calculation depends on $J$ through decreasing functions of its members. With at most $j$ exceptional primes its worst case therefore uses the first $j$ primes after 73.

| Maximum number below cutoff | Cutoff | Worst exceptional set | Outward total upper bound |
|---:|---:|---|---:|
| 0 | 1,100 | empty | 0.962303 |
| 1 | 1,600 | 79 | 0.992898 |
| 2 | 3,200 | 79, 83 | 0.981172 |
| 3 | 500,000 | 79, 83, 89 | 0.999774 |

Use $k=22$ and $\delta=1/3$ for all four rows. Removing a hypothetical fourth prime below 500,000, for example, makes the last row apply no matter how many primes are added above that cutoff. An independent review checked nesting, the second moment, conditional reweighting and the infinite-tail argument. The first-moment and second-moment checkers use exact rational certificates. This theorem has no complete Lean formalization.

```sh
python3 frozen_prefix_tail.py --split 22 --delta 1/3 --cut 1100
python3 frozen_prefix_tail.py --split 22 --delta 1/3 --cut 1600 --small 79
python3 frozen_prefix_tail.py --split 22 --delta 1/3 --cut 3200 --small 79 83
python3 frozen_prefix_tail.py --split 22 --delta 1/3 --cut 500000 --small 79 83 89
```
