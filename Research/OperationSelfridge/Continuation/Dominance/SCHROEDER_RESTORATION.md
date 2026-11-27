# Restoring high-support moduli to Schroeder's measure

In every finite covering of the integers by pairwise distinct odd moduli greater than one, at least **13 different numerical moduli** have four or more distinct prime factors. At least **five** such moduli have all their prime factors at most one billion.

These are direct quantitative consequences of the bounds in the proofs of Theorems 1.1 and 1.2 of Michael Schroeder, *Noncoverage for Distinct Odd Moduli with at Most Three Prime Divisors*. Schroeder already proves that at least one such modulus has all prime factors at most one billion. We use his published margins and threshold table. This note does not independently verify the preprint's full calculation. [Paper, §§2, 4, 7–8](https://michaelschroeder.ai/research/ThreePrimeDivisors/three_prime_factors_per_modulus.pdf)

For the first count delete all labels with at least four prime factors. For the second delete just such labels whose largest prime factor is at most one billion. Keep the original full CRT period, including coordinates that are unused by the residual family. Apply the appropriate published measure there. Its omitted mass is strictly greater than 62924/1000000 and 26213/1000000 respectively. These are margins under the constructed probability measure. The coordinate bound of §2 and preservation of earlier marginals give each deleted class measure at most
$$
 W(m)=\frac1m\prod_{p\mid m}\frac{p-1}{(p-2)(1-\delta_p)}.
$$
The thresholds are precisely those of Table 1. Enlarging coordinate heights beyond those of the residual family is harmless, either in its kernels or by independent uniform extension of the unused digits. Restoring classes to cover the missed set therefore requires the sum of their weights to exceed the indicated margin.

The [checker](schroeder_counts.py) ranks the weights of odd integers with at least four distinct prime factors. Write C(p) for the prime factor in the numerator of W. It verifies C(p)² ≤ p for every prime in the table except 3, where C(3)²=4. From 67 onward C(p)=2(p−1)/(p−2) decreases. Thus W(m)² ≤ 4/(3m). To check every weight of at least 1/700 it suffices to enumerate m ≤ 1000000. Moreover if m has a prime factor at least 211, that prime costs at most C(211)/211, and the other primes contribute at most the product of the three greatest first-power weights. This puts the total below 1/700. The remaining enumeration branches on primes through 199 and their powers. Every additional prime or higher exponent strictly decreases weight.

The largest twelve weights sum to 451763842318/7289602429725, below the first margin. The largest four sum to 37445752/1527701175, below the second. This ranking permits the entire odd range in both counts and so is valid for the restricted set of labels in the second case as well.

Run `python3 Dominance/schroeder_counts.py` from the continuation directory. [Exact transcript](schroeder_counts.txt)
