# An averaged tail bound on the actual 3,5-head holes

**Period restriction.** Suppose a finite family of classes has distinct odd numerical moduli greater than one and covers all integers. Let $Q$ be its period (the lcm of its moduli). If $7\nmid Q$ and the four normalized head classes are in orbit $r=2$, then $23\mid Q$. All exponents and all other prime divisors are unrestricted. The companion orbit-1 argument gives the same prime divisibility in that orbit.

**Further restrictions.** Let $h$ be the ordinary density escaping all classes supported on $3,5$. In orbit 2, omitting 29 from the period requires $h<53/200$, omitting 31 requires $h<27/100$, and omitting 37 requires $h<111/400$. In particular, omitting either 29 or 31 forces all three *numerical moduli* 25, 27 and 45. In both these omission cases the residue of the 27-class modulo 9 is 5 or 8. In the no-29 case the residue of the 25-class modulo 5 belongs to $\{2,3,4\}$. Omitting 37 forces numerical modulus 27. With all primes from 11 allowed, a covering requires $h<33/100$ in orbit 1 and $h<31/100$ in orbit 2. These last bounds concern any putative full covering. The infima $11/40$ and $1/4$ over the head families alone remain sharp.

## Proof

We use the normalized four classes and the head lower bounds from [PHASE_ORBITS.md](../PHASE_ORBITS.md). The lower bound in orbit 2 already follows by subtracting the mixed-class mass $1/8$ from the complement of the two independent pure-power unions, of respective masses at most $1/2,1/4$. Deleting the numerical modulus 25 improves that lower bound to $1/4+(1/2)/25=27/100$. Deleting 27 improves it to $1/4+(3/4)/27=5/18$. Deleting 45 improves it to $1/4+1/45=49/180$. This proves the individual-modulus corollaries once the strict upper bounds on $h$ are shown. A class forced in this way cannot be redundant in a full cover in the specified branch, since deletion would give a counterexample to the same implication.

Write $H$ for the low residues modulo 45 outside the four classes. It has $n=17$ cells in orbit 2 and 18 in orbit 1. On the full head take the uniform probability law $P$ conditional on membership in $H$. Given a proposed lower bound $h_0$ on the ordinary measure of the actual head holes, put $s=45h_0/n$. Choose one subprobability $\lambda\le P$ of mass exactly $s$ supported on the actual holes, for example by uniformly scaling $P$ restricted to them. The same subprobability is used at all tail stages. On the remaining coordinates use ascending-prime distortion, starting with $\lambda/s$. It suffices to prove that the distortion losses multiplied by $s$ sum to less than $s$.

Fix a stage prime $p$, set $g=(1-\delta_p)^{-1}$, $t=(p-1)\delta_p$, and first condition on the entire head point. The conditional caps for the preceding *rough* prime coordinates remain valid, since the distortion at each of their fibres was defined conditional on all the previous coordinates, including the head. In the scalar comparison of Dai, Li, Li and Yi, each earlier rough exponent becomes an independent $T_q$ with $\Pr(T_q\ge j)=g_q/q^j$ for $j\ge1$. Once these variables are known, there are at most $z=\prod_{q<p}(1+T_q)$ rough cofactors. Here and below the product starts at 11 and omits specified missing primes. Include zero entries when a candidate cofactor is absent. For each rough cofactor and exponent $e\ge1$ of $p$, its head-label count $B(x)$ is a sum of at most one indicator for each $3^i5^j$, by numerical distinctness. The stage contribution is bounded by $g/(p-1)$ times the average of $z(B(x)-t/z)_+$ over one such group: specifically use Jensen on the hinge with weights $1/z$ on the rough cofactors and $(p-1)/p^e$ on the exponents. Thus we can bound a single arbitrary group's *averaged* hinge. This step permits different actual phases in every group.

For any $u\ge y$ one has
$$
 \int(B-y)_+\,d\lambda\le s(u-y)+\mathbb E_P(B-u)_+.
$$
Only the second expectation uses the unrestricted head digits. Given the low cell in $H$, compare the higher 3- and 5-digits by the same scalar convex comparison, now with $\Pr(T_q\ge j)=q^{-j}$. These digits were independent and uniform under $P$. Finite head heights can be extended in the upper comparison, and no assumption is placed on them. Writing $a=1+T_3,b=1+T_5$, the possible numbers of labels projecting to each low modulus $1,3,9,5,15,45$, in this order, are bounded by
$$
 v(a,b)=(1,1,a,b,b,ab).
$$
Each such label uses a fixed low residue. For any set $A\subseteq H$ and each listed modulus $d$, define $M_d(A)=\max_c|A\cap(c\bmod d)|$. The positive-part identity over subsets gives the following upper bound on the conditional hinge for all choices of low phases:
$$
 \frac1n\max_{A\subseteq H}\{v\cdot M(A)-u|A|\}.
$$
Indeed, if each phase is independently free, this is its exact supremum. Using the supremum after conditioning on high comparison digits is an upper relaxation.

Write $m=\mathbb E[v\cdot M(H)]/n$ using the **unbounded** geometric tails. The upper bound on $\mathbb E_P(B-u)_+$ can be written $m-u+C(u)$ with
$$
 C(u)=\frac1n\mathbb E\max_{A\subseteq H}
   [u(n-|A|)-v\cdot (M(H)-M(A))].
$$
Every coordinate of the vector of deficits is nonnegative. Replacing $a,b$ by $\min(a,10),\min(b,10)$ increases $C$, while $m$ stays at its true uncapped value. Call the resulting upper correction $C_0(u)$. For each of the 100 exponent pairs the finite maximum is convex piecewise affine, with slopes between 0 and 1. The checker takes its exact upper hull; its slope changes give a probability distribution $Y$ on nonnegative rational breakpoints such that $C_0(u)=\mathbb E(u-Y)_+$ for $u\ge0$.

Take $u=\max(y,u_0)$, where $u_0$ is a $1-s$ quantile of this distribution. Remove its lowest mass $1-s$, splitting the quantile atom if needed, to obtain a subprobability $\nu$ of mass $s$. The bound above now reads
$$
 \int (B-y)_+\,d\lambda\le
 m_* -s y +\int(y-b)_+\,d\nu(b),\qquad
 m_*=m+C_0(u_0)-(1-s)u_0.
$$
This follows directly on each side of $u_0$. In particular the construction does not presume that different tested groups have compatible extremal phases or that the actual head holes occupy a prescribed subset of the low cells.

Substituting $y=t/z$, the unnormalized stage loss is at most
$$
 \frac{g}{p-1}\left(m_*\mathbb EZ-st
    +\mathbb E\int(t-Zb)_+\,d\nu(b)\right).
$$
The checker retains the uncapped first moment of $Z$ with upward rounding. In the remaining decreasing hinge the factors may be replaced by $\min(1+T_q,10)$. The prefix through 180,000 propagates their product histogram. All masses and accumulated costs round up at scale $10^{20}$. In evaluating the integral with cumulative breakpoint mass and cumulative weighted breakpoint sum, the former is rounded up and the latter down.

Above 180,000, use the unconditional $P$ to bound third moments; $\lambda\le P$. For fixed $a,b$, the third moment of a low count is bounded by ordering all its low projection masks comonotonically with respective sizes $M_d(H)$. Indeed, in the positive triple expansion every intersection has size at most the smallest of its three component sizes. The unrestricted first three moments of $a,b$ suffice. Multiply this moment by those of the earlier rough factors. Formula (16) of Dai et al. for $\delta=3/10$ gives the cubic coefficient $4000/[1701(p-1)^3]$. Propagate the cubic moment through $10^7$, then apply their Lemma 2.10 with $\beta=15,\ell=13,b=664578$ exactly as in the [previous full-tail proof](../Review/JOINT_FIBRES.md). Missing primes change the incoming moment. The full prime index after $10^7$ stays fixed.

For orbit 2 without 23 and $h_0=1/4$, the certificate gives $s=45/68,u_0=4/3,m_*=893/408$ and unconditional head third moment $185151/2176$. The prefix loss is $65797962514143156449/10^{20}$. The middle loss is $56096830242012333/(5\cdot10^{19})$ and the infinite tail is below $0.00000964084$. Thus $1-s+\text{loss}<0.997347$. At least $0.0026535$ mass on the $P$-scale survives, a contradiction. This is a distortion-measure margin; it does not give an ordinary density uniform in the full period.

## Compatibility forced when 29 is absent

In the second orbit with 29 absent the excess above the extremal head gap satisfies $h-1/4<3/200$. This controls where the newly forced classes can sit.

Let $D_3,D_5$ be the sums of the reciprocals of missing pure-power labels of each prime, summing over all positive exponents. Let $D_m$ be the sum for all missing mixed labels. If $L$ is the ordinary density of the intersection of the fixed class $1\bmod 15$ with the union of any chosen pure-power classes, then
$$
 h-\frac14\ \ge\ \frac34D_3+\frac12D_5+D_3D_5+D_m+L .
$$
Indeed the uncovered product of the pure towers has density at least $(1/2+D_3)(3/4+D_5)$. From this subtract at most $1/8-D_m-L$ for mixed classes.

**Exclude one phase of the 25-class.** Suppose the 25-class lies in $1\bmod5$, it loses $1/75$ to modulus 15. Thus $h\ge 1/4+1/75=79/300$. In the tail calculation take $s=(79/300)45/17=237/340$. All head holes avoid that 25-class, so in the unrestricted-hinge term we may replace $P$ by the smaller reference submeasure $P'$ obtained by deleting its cylinder from $P$.

In low cells with 5-root 1, the restriction has mass $4/5$ relative to the original cell. After normalization the remaining higher 5-digit coordinates assign mass at most $(5/4)/5^e$ to a specified higher residue of depth $e\ge1$. Multiplying the associated comparison distribution back by $4/5$ recovers its original mass at every positive exponent, and gives $3/5$ at exponent zero in place of $4/5$. Consequently the low-cell weights in the $b=1$ stratum are multiplied by $3/4$ in those cells. In all other cases the old low-cell weights remain valid. The high 3-digit comparison is unchanged because conditioning acts only on the 5-coordinate. This argument permits every choice of the next 5-digit of the 25-class.

Repeat the finite subset maxima with these weights, retaining the unrestricted first moment in each stratum. At $b=1$ the checker uses integer weights 3 and 4 with denominator $4n$. For $b>1$ it uses weight 1 and denominator $n$. The resulting correction law has total mass $W=P'(H)$; remove its lowest mass $W-s$ in the quantile argument. The unconditional cubic estimate using $P$ still dominates the new estimate since $\lambda\le P'\le P$. The resulting $1-s+\mathrm{loss}<0.997163$, excluding the proposed phase. A 25-class in root 0 was already excluded by redundancy. Thus its only possible roots modulo 5 are 2, 3 and 4. This new conditional restriction leaves the cases with the 25-class in one of those three roots open.

**Force the ternary root of the 27-class.** The same submeasure test rules out a 27-class in $1\bmod3$ when either 29 or 31 is absent. Its overlap with the class $1\bmod15$ has mass $1/135$, so test $h_0=1/4+1/135=139/540$. In affected low cells, deleting the specified ternary upper digit leaves relative mass $2/3$. The new conditional upper-digit cap is $(3/2)/3^e$. Multiplying by $2/3$ recovers every positive-exponent comparison probability. At exponent zero the mass becomes $1/3$ in place of $2/3$. Give the affected cells weight $1/2$ when $a=1$ and retain usual weights otherwise. As in the 25 argument, which particular higher digit the class uses does not change this bound.

For computing the low subset maxima take the affected residue modulo 9 to be 1. For any of the other residues 4 or 7, permuting the three rows $1,4,7\bmod9$ and leaving every other row and every column modulo 5 fixed preserves the low set $H$, the partitions into low congruence classes for each of the six listed moduli, and the cell weights after the corresponding row relabeling. Only this finite enumeration is being identified by symmetry. Use the ordinary unconditional cubic throughout. A prefix through 180,000 suffices when 29 is absent; for the smaller margin with 31 absent the positive-part prefix is extended through 600,000 and the cubic range begins immediately thereafter. The two upper charges are below $0.992$ and $0.9996$, respectively. A 27-class in $0\bmod3$ or $2\bmod9$ would be redundant. Its remaining possibilities modulo 9 are precisely 5 and 8.

## Verification

Run from the continuation directory, using Python's standard library.

    python3 TheoryJoint/orbit_quantile.py no23
    python3 TheoryJoint/orbit_quantile.py no29
    python3 TheoryJoint/orbit_quantile.py no29root
    python3 TheoryJoint/orbit_quantile.py no31
    python3 TheoryJoint/orbit_quantile.py no29ternary
    python3 TheoryJoint/orbit_quantile.py no31ternary
    python3 TheoryJoint/orbit_quantile.py no37
    python3 TheoryJoint/orbit_quantile.py head1
    python3 TheoryJoint/orbit_quantile.py head2
    lake env lean TheoryJoint/HeadQuantile.lean

Each configuration and strict acceptance threshold is in the source. The script uses the previous standard-library sieve and pure-exponent probabilities. The prime comparison, submeasure argument, analytic tail application and resulting universal statements are written mathematics. The rational calculations are exact Python. In the pinned Lean 4.36.0/mathlib environment, HeadQuantile.lean kernel checks the pointwise weighted hinge inequality used for submeasures, the final prime-23 rational margin from its supplied loss fractions, and the rational comparison showing that simultaneous alignments of the 25-class and 27-class with the modulus-15 roots alone exceed the no-29 head budget. Its three #print axioms declarations each report propext, Classical.choice, and Quot.sound. The universal implications remain outside Lean.

Dai et al. develop the distortion comparison and show that an odd distinct cover has period divisible by 45 and minimum modulus at most 9. The phase-sensitive subset envelope and sharp head infima are from the preceding project checkpoint. Restricting the charge to the actual surviving head through the quantile inequality and certifying the numerical implications above are applications in this continuation. A targeted search of the cited preprint and public claim index found no matching period-23 implication. Priority remains provisional. [Primary preprint](https://arxiv.org/html/2611.15110v1) · [Public claim index](https://erdosproblems.ai/wiki/problems/covering_systems/E0007/claims)
