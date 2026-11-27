# A phase-sensitive estimate that remains too large

In each normalized no-7 orbit, take the set $H$ of residues modulo 45 outside the four forced classes. It has 18 cells when $r=1$ and 17 when $r=2$. For a nonnegative weight $c_i$ and a class $C_i$ with low modulus $d_i\mid45$, maximizing over independent phases gives the finite identity
$$\sup_{C_i}\mathbb E_H\left(\sum_i c_i 1_{C_i}-t\right)_+
=\frac1{|H|}\max_{A\subseteq H}\left(\sum_i c_i\max_b |A\cap(b\bmod d_i)|-t|A|\right).$$
Indeed, on a finite space the positive part equals a maximum of sums over subsets. The finite maxima over subsets and phases commute, and each phase then optimizes separately.

The experiment applies this envelope with low moduli $1,3,9,5,15,45$. If $T_3,T_5$ are the counts of usable extra 3- and 5-digits past the low block, the shape multiplicities before the other primes contribute are $1,1,1+T_3,1+T_5,1+T_5,(1+T_3)(1+T_5)$. This keeps low-phase intersections while allowing adversarial placement of the rest of each class. In the two tested schedules, substituting the sharp [head-density bounds](../PHASE_ORBITS.md) gives estimated total charges about **1.130** and **1.152**. A proof by this upper estimate would need a charge below one. These are floating-point diagnostics for this choice of comparison and schedule. They provide neither a bound on actual coverage nor an impossibility result for other measures.

    c++ -std=c++17 -O3 orbit_envelope.cpp -o /tmp/selfridge-orbit
    /tmp/selfridge-orbit 1 optimize
    /tmp/selfridge-orbit 2 optimize

The exact assertions used in the main proof are separated in [the third-prime certificate](THIRD_PRIME.md). Lean additionally checks the affine normalization on the 45-cell block in ThirdPrimeOrbit.lean.
