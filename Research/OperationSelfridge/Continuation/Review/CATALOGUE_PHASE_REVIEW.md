# Harrington phase-catalogue obstruction

The 596 variable addition labels in the archived 3,067-class candidate may all change phase together. Allow all remaining unused odd numerical moduli up through 20,000 free phases as well, and additionally free the original seed classes of moduli 9 and 25. Any such family still misses an integer. Exactly 2,469 original seed classes retain their specified phases. The claim includes every subset of the listed variable labels. It permits additional moduli above 20,000 only when the quantitative criterion below covers them, or when they are already among the original seed or 596 addition labels.

## Independent audit of the matching-polynomial certificate

On the prime-product witness, the surviving original fixed classes have empty intersection with the domain. For an axis of original period $b$ and witness residues $V$, the cylinder cap for power $d$ follows by uniformly lifting to $\mathrm{lcm}(b,d)$. It equals $\frac{\gcd(b,d)}{d|V|}\max_r|\{v\in V:v\equiv r\bmod\gcd(b,d)\}|$. Other axes use uniform residues. A cap-one axis can be dropped by enlarging the original event to ignore it. This observation covers cases where a particular phase gives an empty event.

For each peeled fresh coordinate $q$, assign to it all still-live moduli divisible by $q$. The union of their projections on the $q$-coordinate occupies at most the sum of $q^{-\nu_q(m)}$. A coordinate with sum strictly less than one can choose a residue missing every projection. After removal, unassigned moduli are independent of $q$. This works for each assignment of phases to the labelled catalogue.

For remaining product coordinates, remove single-coordinate events separately and condition each coordinate on surviving. The product law remains independent. Group remaining events of equal support and upper-bound their union by the sum of member caps. The resulting dependence graph is the intersection graph of those supports. Its independence polynomial is the matching polynomial of the support hypergraph evaluated at the negative event weights. For each coordinate set $R$, write $Z_R$ for the polynomial of all supports contained in $R$. Splitting matchings at its least coordinate gives the recurrence in the checker. Multiplication by $10000^{|R|}$ clears denominators after upward rounding each support weight to the grid with denominator $10000^{|S|}$. Positivity for all $R$ at these enlarged weights suffices for Shearer's lemma: $\partial Z_R/\partial w_S=-Z_{R\setminus S}$ if $S\subseteq R$. Induction on $|R|$ gives positivity for every smaller weight vector, including arbitrary event subfamilies, and shows that rounding upward is conservative. The program’s positive mass bounds concern residual coordinates before the peeled primes are extended.

The matching-polynomial checker gives a positive residual margin with all 596 phases free, including when 9 and 25 are freed as well. It separately gives a positive margin when all unused odd moduli up through 6,000 are added with the full seed fixed. The combination of the two changes is inconclusive for that checker.

## Finite distortion certificate for the larger catalogue

Start with the same peeling, single-coordinate conditioning and cap-one projection enlargements. If an axis $p$ has singleton-survival lower bound $s_p$, its new probability cap at $p^e$ is $u_{p,e}=\min(1,\operatorname{localcap}(p,p^e)/s_p)$. The law is supported in the original witness. Assign every remaining variable event to the largest surviving prime in its support. At prime $p$, the covered fraction $\alpha_p$ of the new fibre is at most the sum of $u_{p,e_m}$ times the indicator that every earlier requirement of event $m$ is satisfied.

Apply ascending distortion with parameter zero at empty stages and $1/2$ at nonempty stages. In the tuned calculations use $7/25$ at 11 and $43/100$ at 13 if their stages are nonempty. All these parameters are in $[0,1/2]$. The local reference distribution may be nonuniform. The new conditional caps are at most $\min(1,u_{p,e}/(1-\delta_p))$, and the new mass of the covered part is $(1-\delta_p)^{-1}\mathbb E(\alpha_p-\delta_p)_+$.

For each preceding prime $q$ independently sample a uniform point $U_q$ in $[0,1]$. Replace every test on $q^f$ by the nested event
$$
U_q\le\min(1,u_{q,f}/(1-\delta_q)).
$$
Dai et al.'s convex rearrangement proof (Lemmas 2.4 and 2.5 and Theorem 2.6) applies with these arbitrary nested marginal bounds. Indeed, condition on the earlier original coordinates and later independent replacement coordinates, then apply the weighted indicator comparison one coordinate at a time in reverse order. The finite sum $X_p$ of the stage coefficients times all of these nested indicators gives an upper bound for $\mathbb E(\alpha_p-\delta_p)_+$ via $\mathbb E(X_p-\delta_p)_+$.

For stages below the chosen moment cutoff, the checker enumerates the exact distribution of matching event masks in the independent replacement coordinates using integer weights on common denominators. Above the cutoff it calculates the exact first and second moments of $X_p$. Intersecting two nested indicators on $q$ selects the larger required power. For any $a<\delta_p$,
$$
\mathbb E(X_p-\delta_p)_+
\le\frac{\operatorname{Var}(X_p)+(\mathbb E X_p-a)^2}{4(\delta_p-a)}.
$$
The checker evaluates several rational $a$ and retains the smallest bound. Every finite calculation is exact. For the 20,000 cutoff, 2,239 fresh primes peel away, 22 active primes and 2,013 variable labels remain, and the total distortion loss is at most $0.966320102469$. All phases of the variable classes are arbitrary. Thus positive mass survives under the specially constructed law, and CRT supplies an integer avoiding the family.

## Further additions

The construction also gives a weighted sufficient condition for failure after adding new labels of arbitrary size. Condition each peeled coordinate separately on avoiding all its assigned forbidden prefixes. For extra modulus $m$, take the product $C(m)$ of one cap per prime power $p^e\parallel m$. Active primes use $\min(1,u_{p,e}/(1-\delta_p))$. Peeled primes use $\min(1,p^{-e}/(1-\mathrm{load}_p))$. Other fresh primes use $p^{-e}$, and inactive old primes use their original witness cap. A class with modulus $m$ has mass at most $C(m)$ under the extended distorted law. The initial system leaves mass at least $1-L$, where $L$ is the computed stage-loss upper bound. Therefore an increased family with $\sum_{\text{extra }m}C(m)<1-L$ still has an uncovered integer. This mass is relative to the constructed law.

## Only 49 prescribed phases at cutoff 10,000

There is a larger space of seed phases for which exclusion holds if the small-modulus cutoff is 10,000. The admissible numerical labels include all odd moduli greater than one through 10,000, all products of powers of $3,5,7,11,13,17$ at arbitrary heights, and the 596 addition labels from the archived candidate. Among all the labels, only 49 need prescribed Harrington phases. All other labels may have arbitrary phases. If a prescribed label is omitted, adjoining it in the specified phase enlarges the family, so omission is allowed as well.

For the 10,000 run, the distortion loss is at most $0.729515280256$. Sum the caps $C(m)$ over all old-prime-smooth $m>10000$. The product of the six one-coordinate series, minus the exact finite sum through 10,000, gives an upper bound $0.212634722173$. After the witness period and after leaving the cap-one regime, each local series is a geometric series with common ratio $1/p$. This calculation has no maximum exponent. In particular it pays for arbitrary phase changes at every one of the 2,384 seed moduli above 10,000. The old phases always miss the chosen witness region, and the new phases contribute at most their stated caps.

There are 85 original fixed labels at or below 10,000 after the initial release of 9 and 25. Charge an additional arbitrary phase separately at each of the 36 smallest remaining cap values. The cumulative bound remains strictly below one. Thus only the following 49 numerical labels retain their specified Harrington residues:
$$
\begin{gathered}
3,5,7,11,13,15,17,21,27,35,45,49,51,63,65,75,77,81,105,125,\\
135,147,153,175,189,225,243,245,315,325,343,375,405,441,459,\\
525,539,567,675,729,735,945,1029,1125,1215,1323,1377,1575,2205.
\end{gathered}
$$
A simultaneous integer translation of the prescribed phases gives the same exclusion by translating the covering problem. Exactly 2,422 of the 2,471 original seed phases can therefore move in the indicated catalogue. The independent choices of the other variable phases and all prime-power heights on the old support are unrestricted.

## Replay

Place the checker alongside catalogue_obstruction.py and use the existing Harrington seed implementation in its parent directory. From the continuation directory run

    python3 catalogue_distortion.py harrington_reoptimized.json --through 20000 --move 9 25 --moment-from 53 --tuned
    python3 catalogue_distortion.py harrington_reoptimized.json --through 10000 --move 9 25 --moment-from 53 --tuned --smooth 3 5 7 11 13 17 --release-seed
    lake env lean Review/CataloguePayoff.lean

The Lean proof verifies the quadratic majorant. The product witness, conditioning, scalar comparison and extension to all integers have written proofs. [Dai, Li, Li and Yi](https://arxiv.org/abs/2611.15110)
