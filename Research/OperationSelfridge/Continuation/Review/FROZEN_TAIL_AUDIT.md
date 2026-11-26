# Independent audit of the frozen prefix tail

The distortion argument excludes arbitrarily many fresh primes from the specified allowed set. With cutoff 1250, no exceptional smaller coordinates and distortion parameter $1/4$, I independently replayed the old pair sum $U=3885.3702868523615\ldots$ and the total loss ceiling $0.920412000888$. This is a statement about prefix patterns with all old-only slots held fixed and the old heights unchanged. A set of smaller exceptional primes requires its own successful parameter bound.

Each head point in the positive rational mixture belongs to a certified empty product on its head coordinates. Choose one such product deterministically, then sample tail coordinates independently inside its nonempty masks. For one or two old slots, fixed modes are nested, and a variable assignment specifies both the full low prefix and an exit digit. Their intersection is empty or a phase of the coordinatewise stronger modes. There are $2e+1$ ordered pairs of modes with maximum $e$, counting the free mode as zero. Maximizing the head-phase mass and conditional tail-phase probability separately therefore gives a valid upper bound after averaging the mixture. Its support avoids the entire old frozen layout.

On a fresh prime $p$ of height $h$, the uniform probabilities per prescribed phase are $\lambda_e=p^{-e}$ for $1\le e\le h$ and $\lambda_{h+1}=p^{-h}/(p-1)$. Their sum is $1/(p-1)$. For the previous-coordinate intersections used in the second moment,
$$
\sum_{e=1}^{h+1}(2e+1)\lambda_e
\le \sum_{e=1}^\infty(2e+1)p^{-e}=(3p-1)/(p-1)^2.
$$
The final variable phase term on the left combines the geometric tail from $h+1$ onward using its smallest coefficient. A distorted step caps each conditional event by $\gamma$ times its uniform mass, even if the prefix measure on earlier coordinates is nonproduct. Backward conditioning preserves the marginal on the original mixture. No factor $\gamma$ is needed for an unrestricted earlier coordinate, nor for the uniformly sampled exceptional coordinates. At the current prime, the square of the fibre estimate has products of the individual phase masses. Summing those current modes yields $(p-1)^{-2}$. The quadratic majorant for clipping multiplies the second moment by $1/[4\delta(1-\delta)]$.

For a dyadic block $[n,2n)$ with $n=2^k$, every prime in the block divides $\binom{2n}n$, and $p-1\ge n$. Its prime count is at most $2n/k$ since $\binom{2n}n\le4^n$. At $k\ge s$ this gives the code's second-moment growth exponent $b=2\gamma(3+2/2^s)/s$. Exponential growth within a block is bounded by $(1-b/8)^{-8}$. Summing the resulting geometric series gives the reported infinite-tail upper bound; ordinary computation uses outward integer rounding throughout.
