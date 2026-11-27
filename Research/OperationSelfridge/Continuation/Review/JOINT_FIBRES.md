# A necessary interaction between the 3- and 5-divisible moduli

Let $\mathcal D$ be the numerical moduli of a finite covering by residue classes with pairwise distinct odd moduli greater than one. Write $N_{15}=\#\{m\in\mathcal D:15\mid m\}$. Then the following implications hold.

| Absent numerical moduli | Required $N_{15}$ |
|---|---:|
| 9 | at least 1 |
| 3 | at least 6 |
| 3 and 15 | at least 26 |
| 3, 15 and 45 | at least 41 |
| 3, 15, 45 and 75 | at least 54 |

Consequently, if no modulus is divisible by 15, then 3 and 9 both occur, and their assigned classes must be disjoint. If the class of modulus 9 were contained in the class of modulus 3, deleting the former would give a cover without modulus 9. These conclusions concern individual moduli, for arbitrary primes and exponents.

## Proof

Delete all classes whose modulus is divisible by 15, retaining the full period of the original system. In the 3- and 5-coordinates independently condition the uniform distribution on avoiding the remaining pure prime powers. For 5 the covered fraction is at most $1/4$, hence every specified class modulo $5^e$ has conditional mass at most $\gamma_5/5^e$, where $\gamma_5=4/3$. If 3 is absent the covered fraction on its coordinate is at most $\sum_{e\ge2}3^{-e}=1/6$ and $\gamma_3=6/5$ suffices. If 9 is absent, it is at most $1/2-1/9=7/18$ and $\gamma_3=18/11$ suffices. A prime absent from the original support may be padded harmlessly in an upper comparison. The product of the two conditioned measures avoids every surviving class supported on these two primes.

Process successive primes $p\ge7$ by the ascending distortion procedure of Dai, Li, Li and Yi. Write $T_q$ for independent nonnegative integer variables satisfying $\Pr(T_q\ge e)=\gamma_q/q^e$ for $e\ge1$. At a stage $p$, every cofactor of a newly introduced modulus has 3- and 5-exponents with at least one exponent zero. The count of allowed exponent pairs bounded by $T_3$ and $T_5$ is exactly $1+T_3+T_5$. Distinct moduli allow each cofactor at most once at each $p$-exponent. Summing over $p$-exponents and applying the increasing convex comparison in Theorem 2.6 of the cited preprint gives the upper stage loss
$$
\frac{\gamma_p}{p-1}\mathbb E\big(D-\delta_p(p-1)\big)_+,\qquad
D=(1+T_3+T_5)\prod_{7\le q<p}(1+T_q).
$$
Here and below products over $q$ run over primes. Take $\delta_p=3/10$ except at the ten primes from 7 to 41 where $(p-1)\delta_p$ has the explicitly tabulated value in the checker. At those and all larger primes use $\gamma_p=(1-\delta_p)^{-1}$.

For each $T=T_q$ its first three raw moments are $\gamma_q/(q-1)$, $\gamma_q(q+1)/(q-1)^2$, and $\gamma_q(q^2+4q+1)/(q-1)^3$. Independence gives the moments of $1+T_3+T_5$ by expanding powers. The checker propagates the true first- and third-moment upper bounds. For the positive-part correction it replaces each $T$ by $\min(T,9)$ and uses upper masses for the resulting product histogram. This truncation decreases $D$ and therefore increases $(t-D)_+$. The identity $\mathbb E(D-t)_+=\mathbb ED-t+\mathbb E(t-D)_+$ bounds each loss. All discrete upward roundings use integer scale $10^{20}$. The middle range uses $(4000/1701)\mathbb ED^3/(p-1)^3$. Beyond $10^7$ the checker bounds the tail directly by Dai et al., Lemma 2.10, with $\beta=15,\ell=13,b=664578$. The third moment recurrence is bounded by the required factor $1+15/(p-1)$ there, since $\gamma_p=10/7$ and $(10/7)(7p^2-2p+1)\le15(p-1)^2$ for $p\ge7$. This recomputes the head-specific moment entering the infinite tail.

| Omitted modulus | Loss up through 60,000 | Loss above 60,000 through $10^7$ | Upper bound on infinite tail | Lower bound on surviving mass |
|---|---:|---:|---:|---:|
| 3 | 0.79231378984785196126 | 0.00316429597374516867 | 0.000006754 | 0.204515 |
| 9 | 0.98860698989764276444 | 0.00400325315711701202 | 0.000008544 | 0.007381 |

Thus if 9 is missing, deleting the 15-divisible classes leaves positive mass, proving the first row. For any modulus $m$ previously deleted, the iterated conditional coordinate caps bound the mass of its class by $W(m)=m^{-1}\prod_{p\mid m}\gamma_p$. These still apply to every actual class because the measure was built on the full period. When 3 is missing, the sum over the deleted moduli is consequently greater than 0.204515. Rank possible multiples of 15 by $W(m)$ and bound the largest admissible sum with one fewer than each claimed count. The code enumerates odd multiples through 20,000 and checks that no larger multiple can enter those sums, using $W(m)^4\le3/m^3$. The latter follows from $\gamma_p^4\le p$ except possibly at $p=3$, where $\gamma_3^4\le9$. This proves the remaining rows.

## Verification and priority

    python3 joint_fibres.py 3
    python3 joint_fibres.py 9
    lake env lean JointHead.lean

The exact checker uses only Python's standard library. With the existing Lean 4.36.0 / mathlib environment, the Lean file proves the count of allowed exponent pairs and the two rational mass margins. The analytic comparison, its application to arbitrary systems, and finite enumeration are part of the written and computational proof. Preliminary literature checks compared the conclusions with the classical lcm divisibility results, the Dai et al. preprint and the public claim ledger. No matching individual-modulus disjunction was identified there. Priority is provisional.

[Dai, Li, Li and Yi](https://arxiv.org/abs/2611.15110) · [Erdős #7](https://www.erdosproblems.com/7) · [Public claim ledger](https://erdosproblems.ai/wiki/problems/covering_systems/E0007/claims)
