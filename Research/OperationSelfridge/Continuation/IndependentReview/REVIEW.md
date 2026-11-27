# Independent checks

The 23-divisibility argument in the second normalized no-7 orbit was replayed on the full rough-prime range. The exact upper charge is less than 0.997347. The [replay transcript](orbit_replay.txt) gives the rational prefix, middle and final-tail terms. I checked the order of conditional comparisons, use of one fixed head submeasure, positive hinge and quantile, monotonicity of truncations, conditional rough-prime caps and the full prime index. The submeasure permits arbitrary correlations among the surviving head digits.

The [independent head calculation](orbit_head.py) uses the 9×5 CRT product, enumerates subsets with projected-frequency tables, and reconstructs each hinge from ties among all rational pairs of affine functions. It compares all retained atom masses, the adjusted mean and the unconditional third moment to the main checker for six unweighted test cases. For the 23 test the exact adjusted mean is 893/408, the unrestricted third moment is 185151/2176, and all 77 retained breakpoints match. [Head transcript](orbit_head.txt). This head check does not independently derive the entire analytic distortion theorem.

I inspected the proof of the bounded rough-height conditions and the affine interpolation in the pure 3-root weight. The interpolation applies to the unrounded comparison before certifying both endpoints. For the first orbit's joint savings I checked the reference and common kernels against Dai et al., Section 3.3, the three-piece first-difference calculation, the direction of truncation and the lower rounding of the finite sums. Complete admissible comparison columns can dominate a sparse finite input by the published increasing joint comparison, with omitted primes handled consistently.

The [relocation replay](relocations.py) reconstructs all six archived layouts based on the preexisting latest and scored rank-24 candidates. For each recorded unary change it checks containment and disjointness by exhaustive local atom sets. For every one of the 1,343 and 160 mixed relocations it checks that the old rectangle lies in the retained unary union and that the new rectangle meets the remaining product. The independent arithmetic generator checker then verifies the stated integer hole of each layout and counts its generator-defined classes. [Integer and generator transcript](relocations.txt).

I inspected the finite repair solver's search invariant. The active words avoid all unchanged low-arity phases and all previously added phases. Any completion has a remaining phase hitting at least the ceiling of the active size divided by the remaining edit budget. The solver enumerates every such low-arity replacement and relaxes each higher-arity replacement to a shallow triple. Losing an old phase correctly recomputes which further words become active. The product separator tests coverage by the union of patterns and allows different patterns to cover different product points. These arguments concern the stated finite alphabet and repair budgets.

From the continuation directory run:

    python3 TheoryJoint/orbit_quantile.py no23
    python3 IndependentReview/orbit_head.py
    python3 IndependentReview/relocations.py
    python3 IndependentReview/common_hole.py
    python3 IndependentReview/group_counts.py

The additional prime-incidence proofs and their exact quantifiers appear in [the grouped count](GROUP_COUNTS.md) and [the pair and singleton counts](COMMON_HOLE.md).
