# Infinite ternary words avoiding Cartesian-tree squares

There is an infinite word on the ordered alphabet $0<1<2$ in which no two adjacent blocks of the same length at least three have the same Cartesian tree. This proves the ternary $3^+$ entry conjectured in Table 2 of Shibata, Mieno, Köppl, and Inenaga’s *Relaxation of Square-Freeness*, arXiv:2607.00674v2 (accepted for PSC 2026). Table 1 identifies this case as open. Searches for follow-up papers and counterexamples through November 25, 2026 found no earlier resolution. [Paper, Tables 1 and 2](https://arxiv.org/html/2607.00674v2)

## Construction

Apply the following uniform morphism to any ordinary square-free ternary word, where ordinary squares are repetitions of an identical nonempty block. The formalization constructs an infinite ordinary square-free word by iterating the classical Leech morphism on `0`.

| Input letter | Output block |
|---|---|
| `0` | `011212111121` |
| `1` | `012212111221` |
| `2` | `022212112221` |

The ordered Cartesian tree splits a word at its leftmost minimum and recurses on the two sides. If two blocks have the same tree, then the leftmost minima of corresponding subintervals occur in the same relative positions. To see this, a subinterval containing the root has its leftmost minimum at the root. A subinterval wholly on one side can be handled recursively.

Suppose two adjacent output blocks of length $p\ge12$ have the same tree. Their first 12 positions each contain one zero, and equality of the minimum offsets puts those zeros at the same relative position. Therefore $12$ divides $p$. Write $p=12q$ and use offsets beginning at zero within each code block.

The minimum offsets for two payload queries distinguish all three input letters. Use the interval starting at offset 1 of length 4 and the interval starting at offset 2 of length 3. The resulting offset pairs are $(0,0)$, $(0,2)$, and $(3,2)$, respectively. The same pairs arise at offsets 8 and 9 with the same lengths.

If the halves begin at an offset at most 8, each contains the late pair of queries in $q$ consecutive code blocks, starting in its initial block. If they begin at an offset above 8, each contains the early pair in $q$ consecutive blocks, starting in its next block. Either way, the halves force identical consecutive $q$-letter blocks in the input, a contradiction. For half-lengths 3 through 11, the Lean checker exhausts the finite local cases on ordinary square-free inputs. Any such output factor is contained in the image of at most three consecutive input letters.

## Lean verification

`CartesianTreeWords.infinite_ternary_cartesian_square_free` gives an explicit infinite word and proves that every pair of adjacent blocks of equal length at least three has distinct Cartesian-tree shapes. The proof formalizes the leftmost-minimum property, the block arguments, the finite checks, and the infinite square-free source. For the latter, Lean checks the Leech morphism's short cases and that no codeword occurs at an unaligned offset across two blocks. The long cases then reduce to squares in the input by aligning a full codeword and reading the first symbol of each block. The initial letter is preserved, so the iterates are nested prefixes of the infinite source.

```sh
bash Results/CartesianTreeWords/verify.sh
```

The replay uses Lean 4.36.0 and reports the standard axioms `propext`, `Classical.choice`, and `Quot.sound` for the main theorem. The finite checks use kernel reduction.

[Definitions and Cartesian-tree proof](Basic.lean) · [Finite certificates](Certificates.lean) · [Main theorem](Result.lean)
