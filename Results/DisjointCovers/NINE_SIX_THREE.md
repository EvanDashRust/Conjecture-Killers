# The optimal threshold for 9–6–3 covers

Every integer length \(n\ge25\) admits an incongruent restricted disjoint covering system on \([1,n]\) with three consecutive positions assigned the moduli 9, 6, and 3 in that order. There is no such cover of length 24. Thus 25 is the least threshold from which every length is possible.

Paul R. Emanuel posed the eventual-existence question in 2011. In 2012, Laura Lyman, Tim Morris, and Bridget Toomey stated the exact bound \(n\ge25\) as Conjecture 1. They reported constructions for every length from 25 through 490 and no construction at length 24. A literature search on November 25, 2026 found no prior proof of the statement for all lengths. [Emanuel, *Covering systems*, §2.4.0.2](https://doi.org/10.25949/19441907) · [Lyman, Morris, and Toomey, *Incongruent Restricted Disjoint Covering Systems*, §§4, 6–7](https://www.laura-lyman.com/uploads/3/9/7/4/39745896/correctirdcspaper.pdf)

## Construction

Across the interval \([0,n)\), two residues modulo 3 each contain \(k=\lfloor(n+1)/3\rfloor\) points. When \(n\ge395\), we have \(k\ge132\). The preceding result provides two covers on \([0,k)\).

- One cover has modulus 2 and avoids all multiples of 3. It is obtained by doubling a smaller cover that also avoids multiples of 3.
- The other uses only multiples of 3 and contains modulus 3 itself. Each step of the tripling construction introduces that modulus.

The two covers have disjoint modulus sets. Lift them onto the equal-sized residue classes, multiplying their moduli by 3, and use modulus 3 for the third residue. The moduli 2 and 3 of the smaller covers become 6 and 9. Order the three residue classes so that the 9 class, the 6 class, and the 3 class occur in that order modulo 3. Among the two lifts of the 9 class in one period of 18, exactly one is followed immediately by a point in the 6 class. Its next point lies in the 3 class. Translating by one gives the requisite consecutive points on \([1,n]\).

The proof checks lengths 25 through 394 using 29 explicit certificates. Each certificate can cover a range of lengths. Lean checks that every class already has two hits at the lower endpoint and that each integer through the upper endpoint belongs to exactly one class. It checks the ordered 9–6–3 occurrence at the lower endpoint as well.

For length 24, the search fixes the first position of the 9–6–3 occurrence modulo 18, then tries each compatible congruence class at the next uncovered position. Lean proves that a valid cover would make the search succeed and evaluates all 18 initial residues to failure.

## Verification

Replay from the repository root with Lean 4.36.0 available through Elan.

```sh
bash Results/DisjointCovers/verify.sh
```

- [The unbounded construction](ThreePattern.lean)
- [The certificates and theorem for all \(n\ge25\)](PatternCertificates.lean)
- [The impossibility at 24 and least-threshold theorem](PatternOptimal.lean)
