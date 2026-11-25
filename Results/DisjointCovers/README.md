# Disjoint congruence covers without modulus 2

**Gerry Myerson’s second question has an affirmative answer.** For every integer \(n \ge 17\), there is a set of distinct moduli \(m_i\ge 3\) and associated residue classes that partition \(\{1,\ldots,n\}\), with each class containing at least two integers from the interval. For every \(n\ge132\), all moduli can be multiples of 3.

[Myerson’s MathOverflow post](https://mathoverflow.net/a/499017) asks the question explicitly. The post and its updates were checked on November 25, 2026, alongside searches for the exact statement and later work on incongruent restricted disjoint covering systems. No prior solution to the second question was found in those checks. The related unrestricted existence theorem and doubling construction are due to [Gerry Myerson, Jacky Poon, and Jamie Simpson](https://doi.org/10.1016/j.disc.2009.02.002). [Laura Lyman, Timothy Morris, and Bridget Toomey](https://www.laura-lyman.com/uploads/3/9/7/4/39745896/correctirdcspaper.pdf) also describe the tripling construction using two covers with disjoint modulus sets.

## Proof

Work on \([0,n)\) and translate by one at the end. A pair \((m,a)\) records the class \(x\equiv a\pmod m\) with \(0\le a<m\). The condition \(a+m<n\) ensures that the class has at least two points on the interval.

1. **Covers with no modulus divisible by 3.** The first induction uses a table for lengths 44 through 87. For \(n\ge88\), the even points are the image of \([0,\lceil n/2\rceil)\) under \(y\mapsto 2y\). Double its moduli and residues, then use \(1\bmod 2\) for the odd points. The transformed moduli are at least 4, and doubling preserves coprimality with 3.
2. **Covers with every modulus divisible by 3.** Two of the three residue classes modulo 3 in \([0,n)\) have size \(k=\lfloor(n+1)/3\rfloor\). For \(n\ge132\), we have \(44\le k<n\). If \(k<132\), use the table of two covers of length \(k\) with disjoint modulus sets. Otherwise use the first induction for one cover and the second induction for the other. The modulus sets are disjoint because the first contains no multiple of 3 and the second contains only multiples of 3. Lift the covers to the two chosen residue classes by mapping \((m,a)\) to \((3m,3a+r)\) on the fibre \(r\bmod 3\), and cover the third fibre by a single class of modulus 3. The lifted moduli are at least 6.
3. The remaining lengths 17 through 131 have explicit covers with all moduli at least 3. Translating the resulting covers by one gives the stated interval. Distinctness lets the moduli be listed in increasing order.

The finite lists were found by a SAT search. Each candidate class supplied one Boolean variable, each point was constrained to exactly one selected class, and each modulus was constrained to appear at most once. Lean checks every stored witness for the relevant conditions by reduction.

## Verify

From the repository root, with an Elan-managed Lean available on `PATH`:

```sh
bash Results/DisjointCovers/verify.sh
```

The proof uses Lean 4.36.0 with its bundled libraries. [Proof.lean](Proof.lean) exports `DisjointCovers.myerson_second_question` on the original interval and `DisjointCovers.multiple_covers` for the stronger construction. [Construction.lean](Construction.lean) proves the lifting rules, [Checker.lean](Checker.lean) proves the certificate checker sound, and [Tables.lean](Tables.lean) contains the witnesses. The audit reports `propext`, `Classical.choice`, and `Quot.sound` for both theorems.
