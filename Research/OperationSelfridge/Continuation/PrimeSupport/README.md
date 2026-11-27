# How many primes would a no-7 cover need?

Let a finite family of residue classes cover the integers with pairwise distinct odd moduli greater than one. Let Q be their least common multiple and suppose 7 does not divide Q. In the normalized orbit with r=1, Q must have at least **225 distinct prime factors**. In the other orbit it must have at least **75**. Arbitrarily large primes and arbitrary prime powers are allowed. The bounds count actual prime divisors of the period, including 3 and 5. For the sharper second-orbit certificate also run `python3 SliceLearning/rank_review_grid.py`. It uses a grid of sixths, on which every retained head breakpoint is represented exactly. The outward charge for 74 primes is at most 0.999413310243.

Run `python3 PrimeSupport/support_rank.py` from the continuation directory. The threshold numerators used by the proof are in [schedules.json](schedules.json). The [integer transcript](verified.txt) gives the upper charges; exclusion requires a charge strictly below one.

## Reduction to specified prime coordinates

Fix a conjectured upper bound for the number of prime factors. Keep 3 and 5. Replace the remaining primes in order by the same number of smallest primes starting at 11. For an actual prime q and replacement p ≤ q, embed the residue tree of p into the tree of q by interpreting each base-p digit as the identical base-q digit, up to the actual q-height. The preimage of a cylinder is empty or is one cylinder at the same depth. Pull back the cover by the product of these embeddings. Nonempty preimages belonging to different numerical moduli still have distinct exponent vectors, since the prime substitutions are injective. Assigning an unused coordinate or admitting all additional nonnegative weight columns only increases the upper comparison. This reduction is a combinatorial map of residue trees. It does not require this map to be a homomorphism of residue rings.

Write a modulus as d times a part supported on 3 and 5, where every prime dividing d is at least 11. For each nontrivial d, and head point x, let M_d(x) count the classes with that exact rough part that match x on the smooth part. Numerical distinctness allows each smooth exponent pair once for a given d. The phases of classes at the rough coordinates may differ even at the same d.

## The finite-prime comparison

Condition on x. Apply the joint distortion comparison of Dai–Li–Li–Yi, Lemmas 3.1 and 3.2 and equation (34), to these rough coordinates. Repeated projected moduli are legitimate here: each residue indicator is included with its own weight, and replacement by divisibility indicators gives the same comparison indicator for all copies at a given exponent vector. The resulting bound on the sum of losses is an increasing directionally convex function of the finite vector of counts M_d. The initial weights are linear in those counts and all coefficient maps in the induction are nonnegative. Append zero columns where an exponent vector is absent.

If all columns have the same weight m, complete all exponent ranges in the upper model. Every available divisor of an earlier rough comparison integer then makes the same contribution. At a new prime p the total admissible fibre weight is m/(p−1), and an exponent T at p sends the subsequent scalar weight to m(1+T). With r=p−1, threshold t=rδ and c=1/(1−δ), write g=c(m/r−δ)_+ and κ=c when m≥t, otherwise κ=1/(1−m/r). For Kρ F(m)=E[F(m(1+T))] use P(T≥j)=ρ/p^j for j≥1. The backward update is
$$
F_p(m)=g+\max\{K_\kappa F(m),\ K_cF(m)-(c-\kappa)/c\}.
$$
Start at zero beyond the final prime. This is equation (34) with the allowed choice of clipping parameter 1/c. Adding the geometrically summable exponent ranges follows by monotone convergence of the completed finite-weight comparison. There is no omitted large-prime tail: the contradiction assumes a bound on the number of prime coordinates, and the digit embeddings handle every possible choice of their values. The function F is increasing and convex on the scalar diagonal.

For clarity, a single common marginal upper law can be used for all columns. Suppose each of finitely many variables X_i is below Y in increasing convex order. Couple X_i to Y_i with law Y and E[Y_i|X_i]≥X_i, using the submartingale coupling theorem. Given the vector X, sample the Y_i independently from those conditional couplings. Monotonicity and coordinatewise Jensen applied one coordinate at a time give E Ψ(X) ≤ E Ψ(Y_i). Among the couplings of these marginals the common variable Y maximizes the expectation of the supermodular functional Ψ. Thus the diagonal comparison suffices. Finite exponent arrays may be used at this step, followed by the complete scalar upper bound. Directional convexity supplies both coordinatewise convexity and supermodularity. [Leskelä–Vihola](https://arxiv.org/abs/1404.0999) · [Puccetti–Wang, Theorem 2.1](https://sas.uwaterloo.ca/~wang/papers/2015Puccetti-Wang-STS.pdf) · [Dai et al., §3](https://arxiv.org/html/2611.15110v1)

## Two head distributions

In orbit 1 use the independently conditioned pure-power complements on the two small coordinates. The probability z of the larger surviving ternary root belongs to [5/9,2/3]. The class of modulus 15 uses the other root. The total mixed head cost is at most
$$
(4/3)\{(1-z)/5+z/20+1/12\}.
$$
The terms pay for modulus 15, the other mixed moduli of 3-exponent one, and all remaining mixed moduli. The full-period derivation and endpoint argument are given in [the valuation proof](../Alternative/README.md). Each rough column is dominated in increasing convex order by Y=(1+T3)(1+T5) by the coordinatewise congruence comparison. The first ternary survival probability is z, the higher probabilities are 2/3^e, and the positive quinary survival probabilities are (4/3)/5^e. The head charge plus E F(Y) is affine in z for fixed F; checking both endpoints suffices.

In orbit 2 use a common submeasure λ of mass s=45/68 on the actual smooth-head holes, dominated by the uniform law on the 17 low cells with uniform higher digits. The [head hinge proof](../TheoryJoint/HEAD_QUANTILE.md) supplies a finite measure ν of mass s and an error ε≥0 such that for every column and all y≥0,
$$
\int (M_d-y)_+\,d\lambda\le\int(v-y)_+\,d\nu(v)+\varepsilon.
$$
Here ε is the true adjusted first moment minus the first moment of ν. It is strictly below 1/100000. The additive error needs justification before using a joint continuation functional.

Fix the original finite family and η>0. Move a mass (ε+η)/(K−v_max) from the largest atom v_max of ν to K. Choose K above every possible actual column count. For sufficiently large K this raises the right-hand hinge by at least ε at every threshold up to the largest actual count: below v_max the increase is ε+η, and above v_max the factor is (K−y)/(K−v_max), uniformly approaching one on that finite interval. For higher thresholds the left-hand side is zero. Dividing by s gives an honest increasing-convex upper law for each column, by the characterization using positive parts. The preceding coupling argument therefore applies. The diagonal F is eventually affine of slope L. Let K grow and then η decrease to zero. The resulting bound on the integral is ∫F dν + εL. The same submeasure on head holes is used for all rough moduli.

## Exact evaluation

For all m greater than every threshold the backward continuation is exactly A m−B. Its slope updates as A(1+c/r)+c/r and B increases by cδ. This follows by taking κ=c and using E(1+T)=1+c/r. The exact F vanishes at zero; convexity and the eventual slope give the global bound F(m)≤A m and Lipschitz constant A. The verifier rounds the slope upward and B downward. At small integer m the two branches are positive expectation kernels, so inserting upper function values is valid even though the implemented expression algebraically factors their common zero-exponent term. All arithmetic uses integers or rational numbers. For 1+T≥14 it uses the global line, the exact geometric tail mass, and its conditional mean 14+1/(p−1). Between tabulated integers it uses the convex upper chord. For orbit 1 it caps exponents at eighteen only in the finite expectation and pays for the entire omitted first moment at the certified slope.

A [second implementation](../SliceLearning/rank_review.py) reconstructs the head hull and sums the geometric tail exactly on the affine branch. Its charges also lie below one for both ranks. These are written and computer-assisted proofs. No new Lean assertion in this directory claims the prime-count theorem. Schroeder's rank-nine preprint gives a bound without the no-7 hypothesis. Its scope differs from the conditional ranks here. I found no matching conditional rank bounds in the cited primary works or public claim index. Priority remains provisional. [Schroeder, rank-nine companion](https://michaelschroeder.ai/research/NinePrimeSupport/companion)
