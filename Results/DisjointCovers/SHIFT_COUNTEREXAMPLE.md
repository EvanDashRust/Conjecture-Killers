# Counterexample to Emanuel’s two-row shifting conjecture

Paul R. Emanuel’s 2011 thesis asks whether two distinct one-dimensional covers of equal length with identical modulus sets and some shared residues can always be shifted and cropped into a two-dimensional cover. He assumes that neither cover uses the modulus one less than the original length. The answer is **no**. The two covers below satisfy all the hypotheses at length 20, and every pair of equal-width contiguous subintervals fails. I found no prior resolution in a literature search on November 25, 2026. [Emanuel, *Covering systems*, §7.3, p. 127](https://doi.org/10.25949/19441907)

## Counterexample

The intervals here are \([0,20)\). Adding one to each point and each residue gives the equivalent covers on \([1,20]\).

| Modulus | Residue in the first cover | Residue in the second cover |
|---:|---:|---:|
| 4 | 1 | 2 |
| 6 | 4 | 3 |
| 8 | 7 | 5 |
| 9 | 2 | 7 |
| 10 | 8 | 1 |
| 11 | 3 | 8 |
| 12 | 0 | 0 |
| 13 | 6 | 4 |

The covers share the residue modulo 12 and disagree modulo 4. Neither uses modulus 19. Reflecting the first cover gives residue 4 modulo 8. The second uses residue 5.

## Proof and replay

Every potential two-row cover passes two necessary tests.

- The same modulus cannot appear directly above itself. If both \((x,0)\) and \((x,1)\) solve the same \(ax+by\equiv c\pmod m\), then \(b\equiv0\pmod m\). Definition 7.2 requires a nonzero coefficient of the row coordinate.
- Every modulus used after cropping must hit at least three points. Emanuel’s definition also requires those points to be noncollinear.

Checking all 2,470 pairs of equal-width subintervals of width at least two shows that every pair fails one of these tests. The tests are symmetric in the two rows. Each shift and removal of nonoverlapping ends gives one of the checked pairs. The Lean model allows coefficient 1, which appears in Emanuel’s worked examples and only makes the obstruction stronger.

Lean 4.36.0 checks the exact covers, the reduction to these necessary tests, and the complete finite calculation by reduction. The exported theorem is `DisjointCovers.emanuel_shift_conjecture_false`. [Lean source](ShiftCounterexample.lean)

From the repository root, with the Elan-managed Lean toolchain available on `PATH`:

```sh
bash Results/DisjointCovers/verify.sh
```
