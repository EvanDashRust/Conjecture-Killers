# The determinant conjecture for skew finite subsets is false

Kališnik and Lešnik’s Conjecture 6.3 asserts a leading term $4^k r^k$ for the determinant of the similarity matrix on the vertices of the cubical thickening of a skew set $F$. Here $k=2^{N-1}N|F|$. The conjecture appears on p. 23 of the [March 19, 2026 revision](https://arxiv.org/pdf/2603.04271v2).

Take $N=1$ and $F=\{0,d\}$ with $d>0$. This is a skew set because its only coordinate projection is injective. For $0<r<d/2$, the four distinct vertices of the two intervals are $-r,r,d-r,d+r$, in increasing order. Thus $k=2$.

Let $a=e^{-2r}$ and $b=e^{-(d-2r)}$. The similarity matrix $Z$ has entries $e^{-|x_i-x_j|}$. Its entries above the diagonal are products of consecutive factors $a,b,a$. Subtract $a$ times row 3 from row 4, then $b$ times row 2 from row 3, then $a$ times row 1 from row 2. The diagonal of the resulting upper triangular matrix is $1,1-a^2,1-b^2,1-a^2$. In particular,

$$
\det Z = (1-e^{-4r})^2(1-e^{-2(d-2r)}),\qquad
\lim_{r\downarrow0}\frac{\det Z}{r^2}=16(1-e^{-2d}).
$$

The last limit uses the derivative of $1-e^{-4r}$ at zero. Since $e^{-2d}>0$, the conjectured coefficient $16$ is strictly too large for every such pair. A remainder $O(r^3)$ would give the limit $16$ after division by $r^2$.

[Proof.lean](Proof.lean) checks the ordered vertices, the exact determinant, the right-hand limit, and the negation of the claimed big-O statement. The continuity theorem in the paper follows from the corner-system argument in §6.

## The leading coefficient in every dimension

The same calculation extends to a finite skew set of $m$ centers. Write $Z_F$ for the similarity matrix of the centers and $q=e^{-2r}$. For each center, apply the orthonormal Walsh basis of its $2^N$ sign vectors. The diagonal block before the change of basis is the $N$-fold tensor power of the two-by-two matrix with diagonal 1 and off-diagonal $q$. In the Walsh basis the diagonal entries are
$\lambda_S=(1+q)^{N-|S|}(1-q)^{|S|}$ for $S\subseteq\{1,\dots,N\}$.

For two different centers $p,p'$, the signs of the coordinate differences are fixed throughout both cubes. This makes the off-diagonal block a rank-one matrix, with factors of the form $\exp(\pm r\sum_i\epsilon_i s_i)$ and scalar $e^{-\|p-p'\|_1}$. The Walsh coordinate of either factor at $S$ is $O(r^{|S|})$, since each coordinate in $S$ contributes a factor $\sinh r$ and each outside $S$ a factor $\cosh r$. Its constant coordinate tends to $2^{N/2}$.

Now divide both the row and the column indexed by $S$ at each center by $\sqrt{\lambda_S}$. The resulting matrix has the following blocks when the constant modes are placed first.

- The constant-mode block is $Z_F+O(r)$.
- The nonconstant-mode block is $I+O(r)$.
- The two blocks between constant and nonconstant modes are $O(\sqrt r)$.

The Schur complement of the nonconstant-mode block is $Z_F+O(r)$, so the scaled determinant is $\det Z_F+O(r)$. Undoing the scaling multiplies the determinant by $\prod_S\lambda_S^m=(1-e^{-4r})^k$. Consequently the corrected expansion is

$$
\det Z_{C^F(r)^{(0)}}=4^k\det(Z_F)\,r^k+O(r^{k+1}).
$$

By strict Hadamard inequality, the missing factor is less than 1 when $m>1$, because $Z_F$ is positive definite with unit diagonal and positive off-diagonal entries. This section is a mathematical derivation. The Lean file verifies the two-center counterexample in dimension one.

The [arXiv record](https://arxiv.org/abs/2603.04271) still pointed to v2 on November 26, 2026. Searches by the paper title, arXiv identifier, authors, and conjecture number found no earlier public resolution of Conjecture 6.3.

Run `bash Results/SkewMagnitude/verify.sh` with Lean 4.36.0. The optional argument is a mathlib checkout at `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. [Verification transcript](VERIFICATION.txt)
