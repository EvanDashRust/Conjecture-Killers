# Exact density obstruction for the two normalized 3,5 heads

Suppose 7 does not divide the period of a hypothetical odd distinct cover. The [third-prime analysis](Review/THIRD_PRIME.md) forces, after an invertible affine change on the period, the four classes $0\bmod 3$, $0\bmod5$, $1\bmod15$, and $r\bmod9$, where $r=1$ or $2$. Consider only the moduli supported on 3 and 5. Over **all finite** choices of distinct such moduli with these four phases, the sharp infimum of the ordinary density left uncovered is $11/40$ in the first orbit and $1/4$ in the second.

To prove the lower bounds, let $A$ and $C$ be the unions of the pure 3-power and pure 5-power classes. Their local densities are at most $1/2$ and $1/4$, respectively. Under the uniform CRT law their complements are independent. The sum of all mixed class densities is at most $\sum_{a,b\ge1}3^{-a}5^{-b}=1/8$. Subtraction gives $1/4$ in both cases.

If $r=1$, write $X$ and $Y$ for the unconditional 3-adic densities of $A$ in the roots 1 and 2 modulo 3. Then $X\ge1/9$, $X+Y\le1/6$, and $Y\le X$. Modulus 15 loses $X/5$ of its mass to $A$. At every exponent $b\ge2$, a class of modulus $3\cdot5^b$ loses at least $Y/5^b$, because all three 3-roots have $A$-density at least $Y$. If such a modulus is missing, its entire nominal mass can be removed from the upper estimate instead. Hence the uncovered density is at least
$$
(2/3-X-Y)(3/4)-1/8+X/5+Y/20
=3/8-(11/20)X-(7/10)Y\ge11/40.
$$

For sharpness, use a depth $h\ge2$. Assign one class to every pure and mixed exponent through $h$. In both orbits let the pure 3-tower be $0\bmod3$, $r\bmod9$, and $5+3^{a-1}\bmod3^a$ for $a\ge3$. Let the pure 5-tower be $0\bmod5$ and $2+5^{b-1}\bmod5^b$ for $b\ge2$. For the mixed label $3^a5^b$, use 5-phase $E_1=1$ or $E_b=3+5^{b-1}$ for $b\ge2$. The $E_b$ classes are disjoint from the pure 5-tower and from one another.

| Orbit and 5-exponent | 3-phase at $a=1$ | At $a=2$ | At $a\ge3$ |
|---|---:|---:|---|
| $r=1$, $b=1$ | 1 | 2 | $8+3^{a-1}$ |
| $r=1$, $b\ge2$ | 2 | 4 | $7+3^{a-1}$ |
| $r=2$, every $b$ | 1 | 8 | $5+2\cdot3^{a-1}$ |

For each $b$ the mixed 3-tower is internally disjoint, since larger exponents either use disjoint low roots or different first nonzero digit positions after the displayed offset. In the second orbit it avoids the entire pure 3-tower. In the first orbit the $b=1$ mixed tower intersects the pure tower precisely on $1\bmod9$. For $b\ge2$ the intersection consists precisely of the pure classes at exponents $a\ge3$. Thus the displayed lower bounds become equalities in the limit $h\to\infty$. The notes assert an infimum over finite families, with no assertion of attaining the limit at finite depth. [Exact finite grid verifier](phase_orbits.py)

This identifies a limitation of a proof based solely on uniform head density. In the second orbit the prescribed four phases allow the full extremal overlap pattern. A proof that 7 must divide the period needs information about how the remaining prime-dependent classes intersect these head holes.
