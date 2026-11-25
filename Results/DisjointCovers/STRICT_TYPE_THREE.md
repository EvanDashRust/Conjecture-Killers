# Type 3 covers with the printed strict coefficient bounds

Every width $n\ge262$ admits a two-row Type 3 incongruent restricted disjoint covering system with both rows near covers and with $1<a,b<m$ and $\gcd(a,b)=1$ in every defining congruence $ax+by\equiv c\pmod m$. This answers Emanuel’s §7.4.1 question under the literal bounds in Definition 7.2. [Original thesis, printed pp. 112, 126 and 134](https://ndownloader.figshare.com/files/34541747#page=122) · [Source audit](TYPE_THREE_SOURCE_AUDIT.md)

## Construction

Put a near strip of width $\lceil n/2\rceil$ in the even columns of both rows. Use the strengthened near-strip induction in which no modulus is divisible by 3. Explicit seeds cover widths 37 through 72. Horizontal doubling preserves avoidance of multiples of 3, including in the step from $w$ to $2w-1$.

Put a second strip of width $j=\lfloor n/2\rfloor$ in the odd columns. Start with a one-dimensional cover of length $j+1$ whose moduli are multiples of 3 and at most $j-1$. The tripling construction supplies such a cover for $j+1\ge132$. Use its first $j$ points for the lower row and its last $j$ points for the upper row. Each class has a point in both rows. Losing one endpoint in each row could leave a class with only two hits in total only if those endpoints were its only hits, which would require modulus $j$.

Double every modulus and double the residues, adding the parity of the strip’s columns. The two modulus sets stay disjoint. Each doubled modulus is even, and its residues in the two rows are distinct and have the same parity. The near witnesses stay on even columns, including their unhit points outside the interval.

## Strict coefficients

For an even modulus $m$ and two distinct same-parity row residues $l,u$, their difference $d=(l-u)\bmod m$ satisfies $2\le d\le m-2$. It suffices to find $1<a,b<m$ with $ad\equiv b\pmod m$ and $\gcd(a,b)=1$.

Start with $(a,b)=(m-1,m-d)$ and divide by their gcd. This division preserves the congruence since the gcd divides $m-1$. If the reduced second coefficient is 1, write the reduced pair as $(s,1)$ and use $(m-s,m-1)$ instead, then divide by its gcd. This last gcd divides $s-1$, and $2s\le m-1$, so both final coefficients exceed 1. The congruence and coprimality also imply $\gcd(a,m)=1$, which makes the two prescribed row residues exactly the solutions in their respective rows.

## Verification

The main theorem is `DisjointCovers.emanuel_type_three_strict`. The verifier checks the seeds, the parity construction, the strict coefficient argument, and the previous results together.

```sh
bash Results/DisjointCovers/verify.sh
```

- [Strict coefficient lemma](StrictCoefficients.lean)
- [Near-strip seeds and parity construction](NearStrips.lean)
- [Strict Type 3 theorem](StrictTypeThree.lean)
