# Independent review of the prefix-box correspondence

Reviewed the construction and code at 73fb39da9f6158f3d5dff6b154c2afb66f298a2e. The two-way correspondence holds for arbitrary finite odd covers. I found no gap in the stated argument. Individual SAT instances restrict the primes, heights, supports and sometimes unary phases.

## Mathematical checks

For the forward direction choose all primes of the period and use their actual maximum exponents as heights. Each original modulus specifies a unique nonempty fixed-mode vector. For arbitrary low prefixes, CRT supplies an integer attaining all of them at once. The class covering it matches those prefixes. The supplied nonzero exit digits can be arbitrary.

In the reverse direction the original auxiliary indexed by $(p,r)$ deals with an integer equal to $r$ as well as any integer extremely close to $r$ in the $p$-adic metric. If $x$ escapes that auxiliary, $j=x\bmod q$ is nonzero and $x\not\equiv r\bmod p^j$. With $r=x\bmod p^h$ the first unequal digit has index between $h$ and $j-1$. The resulting digit is nonzero. This works for negative integers too. For a core-copy modulus, the exponent at each prime recovers whether the coordinate was free, fixed, or variable. The hypothesis on repeated mode vectors then recovers the chosen pattern, and variable exponents recover the selected copy. Auxiliary labels each have their distinctive fresh prime. All powers in a nonempty mode vector have positive exponents. Each resulting modulus is odd and exceeds one.

A terminal auxiliary with exponents $1,\ldots,q-1$ covers the full cylinder $x\equiv r\bmod p^{q-1}$, including the advertised height-$h$ root if $q-1\le h$. When $q-1<h$ the cylinder is larger than the stated root. The forward implication from a successful restricted search is sound, but failure of a terminal *box configuration* alone need not be failure of the resulting integer family. An integer witness needs to evade the actual terminal classes.

## One auxiliary for all roots

One fresh odd prime $q$ suffices for the ordinary prefix lift, even when $q\le h+1$ for some large heights. Include $0\bmod q$. For each coordinate $(p,h)$, each $r<p^h$ and $1\le j<q$, allocate
$$
e(p,r,j)=h+(q-1)r+j.
$$
Include the CRT class given by $x\equiv j\bmod q$ and $x\equiv r\bmod p^e$. Allocations are injective in $(r,j)$ for each $p$. Auxiliary moduli at different coordinates are distinguished by the other prime factor. For a variable box literal at root $r$, use all exit indices $h\le k<L(p,r)$, where $L(p,r)=e(p,r,q-1)$. The escaping-integer argument above gives the required exit. This allocation can reduce the number of distinct primes in a lifted cover to the number of core primes plus one. It may require larger prime exponents. No minimality assertion about auxiliary count or exponents is needed.

For a pattern with variable coordinates $V$, the number of actual copies is $\prod_{i\in V}(L(p_i,r_i)-h_i)$. There are additionally $1+(q-1)\sum_i p_i^{h_i}$ auxiliary classes. Every copy of a pattern uses exactly its nonfree core primes. These counts are what enter restrictions on divisibility of actual moduli.

An uncovered atom word $(r_p,d_p)_p$ of a nonterminal box gives an integer witness against either generator. Take $x\equiv r_p+d_p p^{h_p}\bmod p^{h_p+1}$ for every $p$, and $x\equiv-1\bmod q$ for each auxiliary (once in the shared version). For every current root the first exit is exactly $h_p$, so a variable class can hit only at that index. At other roots the auxiliary phase $q-1$ has exponent greater than $h_p$ and also misses. This supplies actual integers for transferring constraints across search schemata. Modifying the generator changes which concrete integers escape. Retain the generator identifier together with its evidence.

For the archived 20-coordinate candidate, the original per-root lift has 2,454,012,744 generator-defined classes and this exact hole:
    
    11152137352324005992418108692449707620559016978683297660700581365842899812976857308517305126068836206345900731088916

Using one common auxiliary $q=79$ gives 736,405,734 classes and this exact hole:

    494013294867859399782907899796241

The original counterexample checker tests, for every variable literal, its unique possible valuation against the full allowed interval. It also tests every actual auxiliary at the only possible phase. It uses arithmetic on the generator without expanding billions of CRT classes. The shared checker tests fixed and first-exit residues for every pattern.

A complementary patch uses one common auxiliary to cover multiple residual root rectangles. For each rectangle with CRT period $M$ and residue $a$, allocate $q-1$ nontrivial distinct divisors $D_j\mid M$, with $\gcd(q,M)=1$. Require disjoint divisor labels across rectangles. The $qD_j$ classes use the phase $j\bmod q$ and $a\bmod D_j$, together with the common $0\bmod q$. Keep $q$ fresh from the existing moduli or verify label noncollision directly. The single-rectangle idea is McNew and Setty's divisor-multiple extension and the project's previous Closure.lean already gives that form. Sharing a label at modulus $q$ and allocating the other labels disjointly is a direct extension. No priority claim. [McNew and Setty, Corollary 4.8](https://www.nathanmcnew.com/covering.pdf)

## Verification

PrefixLiftReview.lean checks forward CRT transfer to fixed roots of arbitrary heights, the reverse direction in simultaneous local-congruence form with a common auxiliary, and numerical injectivity of lifted core copies. The formal conclusions use the stated hypotheses on factor supports, repeated mode vectors, allocations and copy legality. The formal file does not package the complete equivalence as one proposition over arbitrary finite families. The written argument identifies the local conjunctions with individual CRT classes and verifies the remaining auxiliary label conditions.

The independent test of the historical generator uses a mixed 2/3 control with 84 classes, comparing the result for all eight subtemplates to exhaustive atom matching. Its integer verifier recursively partitions $x=pt+b$, maps each congruence to the exact corresponding congruence on $t$, and checks every branch. An additional test of the shared generator checks all 207,360 residues of its mixed control, along with explicit failures after each of three pattern deletions. A shared-terminal test exhausts both rectangles over their common period.

Run the scripts beside the archived sources or pass the paths:

    python3 check_original.py ../prefix_lift.py ../prefix_candidate.json
    python3 shared_lift.py ../prefix_candidate.json

For Lean use 4.36.0 and the same pinned mathlib as the prior checkpoint. Build Mathlib.Data.Nat.ChineseRemainder if it is not already cached, compile the original LocalExit.lean and expose its output on LEAN_PATH. Then run lean on PrefixLiftReview.lean. All checked statements use only standard Lean axioms.
