# Multiplicities above a prime cutoff and the archived rank-20 repair problem

**Theorem.** In any finite covering of the integers by moduli greater than one whose prime factors are all at least 79, some modulus occurs at least 26 times. All exponents and the number of prime factors are unrestricted.

**Fibre consequence.** Given any finite odd distinct cover, write $n=ab$ uniquely with all factors of $a$ at most 73 and all factors of $b$ at least 79. Fix the complete small-prime coordinates to any assignment avoiding every class with $b=1$. There exists $b>1$ such that at least 26 classes with that same rough cofactor $b$ match the fixed assignment on their respective smooth parts. Their smooth parts are distinct, since the original numerical moduli are distinct. Indeed, after fixing all small-prime coordinates, the remaining CRT coordinates would otherwise have to be covered with multiplicity at most 25. If there is no surviving assignment, the small-prime classes already cover the integers.

## Distortion estimate

Use all prime coordinates appearing in the rough family in their increasing order. Write $\delta=3/10$, $c=10/7$, and $s=25$. At a new prime $p$, a preceding cofactor $d$ and a positive $p$-exponent specify a whole numerical modulus. It has at most $s$ classes. Before convex comparison there can be $s$ distinct preceding residue indicators for that pair. Applying Dai et al., Theorem 2.6 to the whole list of indicators bounds them by at most $s$ copies of the same event $d\mid R$. The fibre stage mass is bounded by
$$
\frac{cs}{p-1}\mathbb E\left(D-\frac{\delta(p-1)}s\right)_+,
\qquad D=\prod_{79\le q<p}(1+T_q),\qquad \Pr(T_q\ge j)=c/q^j.
$$
Inserting all absent primes in the scalar comparison increases this upper bound. The third moment of $D$ increases at each prime $q$ by the factor
$$
f(q)=1+\frac{10}{7}\frac{7q^2-2q+1}{(q-1)^3}.
$$
The initial moments are both one at the empty preceding product.

In rough_tail.py the prefix through 20,000 uses the true first moment of $D$ and the capped factors $\min(1+T_q,10)$ only in the decreasing correction $\mathbb E(t-D)_+$ in the identity $\mathbb E(D-t)_+=\mathbb E D-t+\mathbb E(t-D)_+$. All probability products, moments and costs are rounded upwards at integer scale $10^{18}$. Large prefix product states can be discarded permanently when they exceed every remaining threshold in the prefix. Through $10^7$, formula (16) of Dai et al. bounds the remaining stages by $(4000/1701)s^3\mathbb E D^3/(p-1)^3$. For the analytic interval above $10^7$, their Section 4.3 already gives an upper bound $0.000008082310506662$ for the baseline third-moment estimates. Relative to their baseline one must remove the initial third moment $31/2$ and the moment factors for the primes from 7 through 73, and multiply by $s^3$. The ratio of the underlying exact moments is constant throughout the tail. This applies even though the published baseline uses outward rounding.

The full upper bound is strictly below $922631528/10^9$. Thus a point survives the rough classes. The theorem invokes the published comparison and infinite-prime tail; the remaining parts are an exact Python computation and the argument above. A separate project reviewer audited the multiplicity and tail scaling.

This uses the existing distortion method. Bounded-multiplicity adaptations for the minimum-modulus problem have precedent. I did not establish priority for the cutoff and the constant. [Dai, Li, Li and Yi, Sections 2 and 4.3](https://arxiv.org/abs/2611.15110) · [On the j-th smallest modulus of a covering system with distinct moduli](https://dms.umontreal.ca/~koukoulo/documents/publications/covering-systems.pdf)

## Concrete application with precisely stated frozen assumptions

Keep the archived prefix_candidate.json phases and all its original lifted congruences. Every addition may contain arbitrary rough factors and arbitrary powers of those rough primes. Suppose its smooth part divides $315=3^2\cdot5\cdot7$. Then the enlarged family cannot be a cover. This result applies both to the original per-root construction and to the shared-prime construction in the companion review.

The fixed prefixes of the archived candidate have periods $9,5,7$. Of the 315 root triples, 195 are covered by fixed unary patterns and a further 45 are covered by other fixed patterns. Two more, $(8,1,2)$ and $(8,1,5)$, are covered by patterns involving digits of those first three coordinates. For each of the other 73 triples, root_evidence.json provides an entire atom word escaping every pattern of the candidate. The file records all coordinates with their prime and height. The independent verifier tests every one of the 315 triples and checks that *all 11 nontrivial divisors of 315* already occur as fixed-only moduli. Consequently a distinct new class whose smooth part divides 315 must have nontrivial rough cofactor.

For any one of those 73 words, fix the concrete small-prime coordinates by
$$
x\equiv r_p+d_p p^{h_p}\pmod{p^{h_p+1}}
$$
for each of the 20 core primes. This is a full integer cylinder on those coordinates, and every refinement of that cylinder avoids all existing core-copy classes. If an existing auxiliary uses the prime $q_{p,r'}$, it contributes its pure $q_{p,r'}$ class after projection. Its other labels are $q_{p,r'}p^j$ with $1\le j<q_{p,r'}$. A projected label can match the fixed assignment only when $j\le h_p$, since every integer in this cylinder has $v_p(x-r')\le h_p$ for **every** root $0\le r'<p^{h_p}$. In the original construction each such auxiliary prime belongs to just one pair $(p,r')$. Hence each rough modulus receives at most $1+h_p\le3$ original projected classes. In the shared-prime construction all allocated exponents exceed $h_p$, leaving only its pure auxiliary class on this cylinder.

Each rough modulus can gain at most $\tau(315)=12$ added classes, because their allowed smooth parts are distinct divisors of 315. Thus even if additions reuse the auxiliary primes, the projected multiplicity is at most 15. The theorem produces a surviving choice of rough coordinates, and CRT joins it to the fixed small-prime assignment. This works on each of the 73 witnessed root triples. Changes to the original phases or new classes with other smooth parts require a fresh argument.

A larger family of smooth alphabets is also excluded. Fix any one core prime $p$ and allow smooth parts dividing $315p$. All nontrivial divisors of $315p$ already occur as core-copy numerical moduli, as the checker verifies by taking copy index $k=h_i$ at every variable coordinate. There are at most 24 divisors. In the shared-auxiliary construction, the resulting rough multiplicity is at most $24+1=25$ on each atom-hole cylinder. For the original auxiliary scheme, use the certified word with root triple $(8,4,5)$. Dropping the surviving original nonpure auxiliary classes leaves multiplicity at most 25. Those dropped classes form one class each of moduli 89, 103, 149 and 179 and two of modulus 113 after projection. In the distortion law for the retained rough system, their total mass is at most
$$
  \frac{10}{7}\left(\frac1{89}+\frac1{103}+\frac2{113}+\frac1{149}+\frac1{179}\right)<0.072775.
$$
The cap on each prime residue is still $c/q$ under the final law, which can use the full rough prime coordinates of both the retained and dropped classes. Adding this mass to $0.922631528$ leaves a strict gap. Thus no such extension of the original frozen lift is a cover. The choice of $p$ is fixed across the proposed additions.

The pointwise multiplicity condition suggests testing the joint compatibility of distinct smooth phases sharing a fixed rough cofactor. Numerical counts of fresh incidences alone lose this information.

## Replay

    python3 rough_tail.py 79 25
    python3 root_projection.py ../prefix_candidate.json root_evidence.json

The projection checker imports the companion shared_lift.py. The rough-tail calculation uses only the Python standard library. The fibre theorem and the application above are written mathematics with computational verification.
