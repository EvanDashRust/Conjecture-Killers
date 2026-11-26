# Infinite binary words avoiding Cartesian-tree squares

There is an infinite binary word in which no two adjacent blocks of the same length $p\ge4$ have the same ordered Cartesian tree. This is the binary $4^+$ entry of Shibata, Mieno, Köppl, and Inenaga’s *Relaxation of Square-Freeness*. Table 1 marks the entry open. Table 2 conjectures an infinite word. The status check used the latest arXiv version and found no earlier resolution in literature searches through November 25, 2026. The separate PSC 2026 proceedings PDF could not be retrieved. [Paper, Tables 1 and 2](https://arxiv.org/html/2607.00674v2) · [Shibata’s publications and conference slides](https://shibh308.github.io/)

## Construction

Start with the infinite ordinary square-free ternary word from [Result.lean](Result.lean), constructed by iterating the classical Leech morphism on `0`. Encode it with the following morphism.

| Input letter | Output block | Leftmost minimum in first four bits | Leftmost minimum in last three bits |
|---|---|---:|---:|
| `0` | `0010101` | 0 | 1 |
| `1` | `1001000` | 1 | 0 |
| `2` | `1110110` | 3 | 2 |

The minimum offsets are relative to the indicated substring and start at zero. Each column of offsets distinguishes all three input letters by itself.

## Proof

A Cartesian tree is defined by splitting a word at its leftmost minimum and recursing on the left and right factors. Equal ordered trees imply matching leftmost-minimum offsets on all corresponding intervals. The shared proof in [Basic.lean](Basic.lean) establishes this by tree induction.

For $4\le p<14$, the two adjacent halves meet at most five code blocks. The certificate checks every square-free ternary input of length at most five, each starting offset in the first code block, and each such half-length. For each window, the halves disagree on the minimum offset of some corresponding subinterval.

For $p\ge14$, the first half contains a complete code block. If the two halves share a Cartesian tree, the matching seven-bit window in the second half shares all subinterval minimum offsets of that code block. The synchronization certificate checks that no unaligned seven-bit window crossing a boundary between two distinct code blocks can do so. Consecutive input letters are distinct by square-freeness. Thus $7$ divides $p$.

Write $p=7q$. Both halves start at the same offset within their respective code blocks. If that offset is at most four, use the three-bit suffix in each of $q$ consecutive code blocks starting with the block that contains the start of the half. If the offset is greater than four, use the four-bit prefix in each of $q$ consecutive code blocks starting with the next block. The two halves have matching minimum offsets on those queries, so the corresponding $q$ input letters agree. Those input factors are adjacent and form an ordinary square, a contradiction.

## Lean verification

[Binary.lean](Binary.lean) proves `CartesianTreeWords.infinite_binary_cartesian_square_free`. Its witness has type `Nat → Fin 2`. The tree definition compares ranks, so the proof passes the two binary letters to the shared tree definition by an embedding that preserves their ranks.

From the repository root, with Lean 4.36.0 on your path, run:

```bash
bash Results/CartesianTreeWords/verify.sh
```

Lean evaluates all finite certificates in its kernel. The replay prints the axioms used by both the binary and ternary theorems.
