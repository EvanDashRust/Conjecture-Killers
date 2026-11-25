# Emanuel’s Type 3 question and the Lean statement

The Lean proof establishes eventual existence with the coefficient convention used in Emanuel’s examples and horizontal doubling. Definition 7.2 prints a stricter coefficient bound. A separate construction now proves eventual existence with the literal bound. [Strict-coefficient theorem](STRICT_TYPE_THREE.md)

## Original source

Paul Robert Emanuel, *Covering systems*, PhD thesis, Macquarie University, 2011. The university distributes the body as `02whole.pdf`, Figshare file 34541747. The checked copy has SHA-256 `0d1f003a77a02f33a58705c90ca590c86dd27db8052741bf3c3f8b6084a980c8`. This file has ten pages before printed page 1. [Repository record and rights statement](https://doi.org/10.25949/19441907) · [Original PDF](https://ndownloader.figshare.com/files/34541747)

| Passage | Printed page | PDF page | Relevant content |
|---|---:|---:|---|
| Definition 7.2 | 112 | 122 | Distinct moduli, exact coverage of the rectangle, and three noncollinear hits per class. The equation is $ax+by\equiv c\pmod m$, with the printed restrictions $1<a,b<m$ and $\gcd(a,b)=1$. The paragraph immediately after the definition discusses dividing out a coefficient gcd when it is invertible modulo $m$. [Original p. 112](https://ndownloader.figshare.com/files/34541747#page=122) |
| Definition 7.9 and Theorem 7.2 | 126 | 136 | A near IRDCS exactly covers $[1,n]$, has at least one singleton congruence, and encounters a collision or an “empty position” on extending either way before every congruence acquires a second solution. Theorem 7.2’s third case pairs a near cover with a full or near cover on the same moduli. [Original p. 126](https://ndownloader.figshare.com/files/34541747#page=136) |
| Horizontal doubling in §7.4 | 128–129 | 138–139 | The thesis uses $x+y\equiv1\pmod 2$ and the analogous congruence with residue zero. The example directly uses $a=b=1$. [Original p. 128](https://ndownloader.figshare.com/files/34541747#page=138) · [Original p. 129](https://ndownloader.figshare.com/files/34541747#page=139) |
| §7.4.1 | 134 | 144 | “It remains to see whether there exist Type 3 $X\times 2$ IRDCS for all $X\ge k$ for some $k$.” [Original p. 134](https://ndownloader.figshare.com/files/34541747#page=144) |

## Requirement-by-requirement comparison

| Source requirement | Lean implementation | Assessment |
|---|---|---|
| Exact one-dimensional coverage on $[1,n]$ | `Strip` requires `exactRow` for both rows on $[0,n)$. Translation by one gives the printed row interval. [`exactRow` and `Strip`](NearStrips.lean#L18) | Equivalent after translation. |
| A singleton and an obstruction to extension in both directions | `NearRow` gives one selected class and two unhit positions. Both positions occur before the same class’s nearest possible second hit in their respective directions. `near_prevents_completion` rules out every larger interval that retains the same congruences, covers exactly, and gives each class two hits. [`NearRow` and completion theorem](NearStrips.lean#L31) | Sufficient and stronger. The thesis permits collisions as well as holes, and the same singleton need not be the one that prevents completion in both directions. |
| Type 3 pairing on common moduli | One `StripClass` stores each modulus with its two row residues. The final theorem requires `NearRow` for both rows. [`StripClass`](NearStrips.lean#L5) · [Main theorem](TypeThree.lean#L139) | Both rows are near, which suffices for Type 3. |
| Exact rectangular coverage and three noncollinear hits | `Strip` enforces modulus uniqueness and exact coverage in each row. Each class hits both rows and twice in at least one row. `Strip.realizes` turns those hits into the required three noncollinear points and matches each modulus label to its linear congruence. [`TwoRowIRDCS`](ShiftCounterexample.lean#L17) · [Realization](TypeThree.lean#L69) | The stated requirements hold. |
| Linear congruences and coprime coefficients | `TwoRowIRDCS` imposes $0<a,b<m$ over natural numbers and $\gcd(a,b)=1$. The realization takes $a=1$ and $b=(r_{\mathrm{lower}}-r_{\mathrm{upper}})\bmod m$ in $[1,m)$. [Coefficient predicate](ShiftCounterexample.lean#L24) · [Coefficient witness](TypeThree.lean#L91) | Matches the working convention of the examples. It permits 1, which the printed strict inequality excludes. |
| Eventual existence | `emanuel_type_three_from_nineteen` proves existence for all $n\ge19$ in the Lean model. [Main theorem](TypeThree.lean#L139) | Supplies a sufficient threshold for the convention used in the construction. |

Every inductive construction at width at least 37 introduces modulus 2. The strict bound $1<a,b<2$ has no integer solutions, so the same system cannot be made strict by choosing different representatives of its coefficients. A proof for the literal coefficient bound requires a different construction at least for those widths. [Modulus-2 step](NearStrips.lean#L91) · [Induction](NearStrips.lean#L313)

The separate §7.3 shifting counterexample rules out a realization under the weaker bounds. Its negative conclusion therefore also holds under the printed strict bounds. [Shifting counterexample](ShiftCounterexample.lean#L155)

Macquarie marks the thesis as in copyright. The links above point to its authorized copy. [Rights statement](https://rightsstatements.org/page/InC/1.0/?language=en)
