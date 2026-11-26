# Operation Selfridge • November 26, 2026

No covering or unrestricted impossibility proof was found. This checkpoint starts from 73fb39da and keeps the previous candidates. All references to a rank below count core prime coordinates of a particular construction. Only the original valuation-box model has the earlier exclusion through rank 19.

## Restrictions on every hypothetical covering

At least **nine distinct numerical moduli** must be divisible by 7 or 11, counting their union once. If 7 is absent from the period, 11, 13, 17 and 19 must all divide it. In that case 3, 5, 9 and 15 must be the actual moduli of four classes, at least 29 moduli are divisible by 11, and at least 50 are divisible by 15. At least 36 of the latter have another prime factor at least 11. These simultaneous necessary conditions allow arbitrary support and exponents. [Proof, rounding and analytic tails](Review/THIRD_PRIME.md)

The four forced classes in the no-7 branch have exactly two possibilities under affine normalization. Their optimal ordinary 3,5-head uncovered densities, as infima over finite heads, are **11/40 and 1/4**. Both values have explicit sequences approaching equality. [Proof and generator](PHASE_ORBITS.md)

## How much freedom can the archived prefix layout tolerate?

Fix the old mode heights, unaries and phases of the 20-coordinate layout in [prefix_candidate.json](prefix_candidate.json). In an extension, every new slot must involve at least one new prime. Permit **every** such mode vector once with a freely chosen phase, every support size, and arbitrary finite prefix heights on the new primes. Any choice of at most **three** new odd primes leaves an uncovered point. With one new prime the obstruction even permits one additional or rephased nonempty old-only slot. Changing the core heights or several old phases can change this conclusion.

Here is a reproducible witness measure for the assertion. Each mask product in [the certificate](Runs/product_mixture.json) is nonempty and lies inside the old uncovered set. For every old pattern, the checker exhibits a coordinate on which the mask excludes its phase. On the first three coordinates give the listed atom triples their indicated rational weights divided by their sum. Conditional on a triple, choose the first certified product containing it in the head, then sample the remaining 17 coordinates independently and uniformly from that product. The canonical alphabet avoids each fixed old unary.

For each old mode vector, bound the largest measure of one phase by the largest mass of its head projection times the largest conditional tail probability among the certified products. On the tail all old heights are zero. A selected tail coordinate therefore contributes the reciprocal of its mask cardinality. Summing the bounds over old mode vectors, including the empty vector, gives

$$T=\frac{90182119145316653296185281101616640791}{3328437906425811053317486484593152000}.$$

Independently put the uniform law on the full atom alphabet of each new prime. At height $h$, each fixed mode $e$ has phase probability $q^{-e}$ for $1\le e\le h$. The variable mode has probability $q^{-h}/(q-1)$. Their sum is exactly $1/(q-1)$ for **every** $h$. The union of all proposed additions consequently covers measure at most

$$T\left(\prod_{q\in F}\frac{q}{q-1}-1\right).$$

The three smallest eligible primes are 79, 83 and 89. Their exact rational bound is less than 0.997662, leaving positive mass. The largest possible phase of any additional nonempty old slot is bounded by its largest possible singleton coordinate. Adding this bound to $T/78$ gives less than 0.989977. Both inequalities can be replayed with `python3 fresh_coordinate_bound.py`. Four fresh primes give an upper bound above one by this calculation.

The second-moment extension handles arbitrarily many fresh primes. If a completion retains these old phases and heights, its four smallest fresh primes must be below 1,100, 1,600, 3,200 and 500,000 respectively. [Proof and infinite-tail certificate](FROZEN_PREFIX_TAIL.md)

A separate restricted patch allocates one fresh multiplier per terminal rectangle and distinct divisor labels for its rows. [The rectangle calculation](terminal_budget.py) gives total rectangle mass at most 0.000084679, while the base has hole mass above 0.00987218 under the same uniform reduced atom law. This defeats a proof by those rectangles. Overlapping arithmetic classes outside the rectangles need separate treatment. The multiple-pattern shared-79 experiment repaired 650 successive row witnesses and still left integer 18890713735657765180238402644797142 uncovered.

## What persists when Harrington phases move?

With Harrington's specified seed fixed, rephasing all 596 addition labels in the 3,067-class layout cannot cover the integers. The 110 mixed additions already present pass the earlier necessary weighted-interaction test. The stronger argument peels coordinates whose total forbidden local mass is less than one, then bounds the total loss on a seed-free CRT product. Two larger exclusions follow.

- Hold 2,469 original seed phases fixed. Allow 9 and 25, all 596 addition labels, and all unused odd moduli up to 20,000 arbitrary phases. The loss is at most 0.966320102469.
- Hold just 49 specified original phases fixed. Allow arbitrary phases on the remaining seed, all 596 addition labels, every remaining odd label through 10,000 and every modulus supported on 3, 5, 7, 11, 13 and 17 with arbitrary exponents. The total upper bound is 0.999208985497. Both claims allow omission of labels.

See the [assumptions, exact checkers, unbounded extra-label budget and 49 labels](Review/CATALOGUE_PHASE_REVIEW.md). Vivian independently developed an obstruction when the graph on fresh primes has disjoint components of size at most two and every paired prime exceeds 239. I replayed her fourth-moment calculation, which gives upper bound 0.322270769143343303. I also reproduced her rank-20 hole and translated her alphabet indices to labelled first-exit digits. [Vivian's argument](Review/VIVIAN_MIXED_PAIRS.md) · [Source point](Runs/source_points.json)

## Universal restrictions and verification

The independent review reproduced the bounds of 18 moduli divisible by 3 and 11 divisible by 5. It checked the ternary tree maximum for budgets through 17 using a separate C++ program and recomputed all 17 critical five-adic pair comparisons on their CRT grids. A joint argument gives a stronger alternative. If no individual modulus is divisible by 15, both numerical moduli 3 and 9 must occur, with disjoint congruence classes. If 3 is absent, at least six moduli must be divisible by 15. These statements allow arbitrary prime factors and exponents. The case with both 3 and 9 disjoint remains. [Independent count review](Review/COUNT_REVIEW.md) · [Joint proof and stronger conditional counts](Review/JOINT_FIBRES.md)

Applying the same large-prime estimate to ordinary numerical congruences gives unrestricted bounds on the positions of prime divisors. At least four distinct primes are below 43, five are below 73, and six are below 277. [Proof and exact checker](PRIME_POSITIONS.md)

A second fibre obstruction applies after every surviving assignment at the primes through 73. Some rough cofactor above that cutoff must occur in at least 26 compatible classes. The same argument gives a multiplicity lower bound of 26 for a covering using only primes at least 79. [Proof, scope and tail estimates](Review/ROUGH_FIBRES.md)

The prefix correspondence was independently reviewed in both directions, including numerical distinctness. A single common auxiliary prime suffices for the reverse lift. The actual class count includes all valuation copies and auxiliary classes. For example, the archived incomplete layout gives 2,454,012,744 numerical classes in the old generator and 736,405,734 in the shared-79 generator. Both have explicit integer counterexamples. The review also isolated 73 triples of low roots each containing an explicit uncovered word. Lean 4.36.0 checks local forward and reverse transfer lemmas, injectivity for the core copies, the head-count identity, rational margins and the quadratic majorant. The analytic bounds and complete two-way equivalence remain written arguments with exact computations. [Prefix review and integer verifiers](Review/PREFIX_REVIEW.md) · [Low-root evidence](Review/root_evidence.json)

## Cumulative constructive searches

The unrestricted-phase SAT searches below include every slot through their given arity. A slot is a nonempty choice of prime coordinates and modes. Distinct phase choices only need separate Boolean literals when a saved point distinguishes them. A sequential at-most-one constraint admits all phases of each slot; any unselected slot can take an arbitrary phase. The exact recursive hole finder checks the whole finite atom space for the candidate returned by SAT. Numerical fields in the checkpoint label every atom with its prime column, low residue and first nonzero digit.

| Search | Constraints | Exact holes retained in this run | Outcome |
|---|---:|---:|---|
| Eight primes, free unary phases, arity 3 | 5,358 | 482 | Timeout |
| Six primes, fixed unaries, height 1 at 3, arity 4 | 1,304 | 177 | Timeout |
| Eleven primes, free unaries, height 1 at 3, arity 3 | 7,433 | 122 | Timeout after carrying the eight-prime run |
| Changed eight-prime list, free unaries, heights 2 at 3 and 1 at 7 | 3,541 | 47 | Timeout after transferring older evidence |
| Old rank 20 with reserve slots and coordinated phase changes | 1,113 | 250 | Explicit hole |
| Rank 23 with movable old phases and 1,100 reserve slots | 1,562 | 80 | Explicit hole |
| Rank 24, adding 97, old phases movable and 1,500 reserve slots | 1,714 | 213 | Explicit hole |
| Rank 24, every unary phase free, a changed small-prime unary required in each repair | 3,562 | 90 | Explicit hole |
| Three-prime sanity check, fixed unaries, arity 2 | 9 | 4 | Finite UNSAT, independently rebuilt CNF, checked DRAT |

The released-unary branch retained the previous root-labelled points on their original primes, then added the translated integer bank across the full alphabets. Every one of its 90 tested proposals changed at least one original unary on 3, 5 or 7. Its last per-root CRT generator yields 32,536,723,404 numerical classes. A separate arithmetic checker verified that the integer in [the audit](Review/results/checkpoint_audit.txt) escapes all of them.

The Harrington integer loop now requires every accumulated escaping integer to be covered before accepting a new candidate. The runs on the original catalogue found 140 holes with the seed fixed and 160 on the separate movable-seed branch. The latter changes 9 and permits 15, 21, 25 and 35 to move together with additions. With 620 more labels of size at least 20,001 and the seed fixed, 179 proposed layouts failed. The final 3,687-class candidate covers all earlier required integers and misses exactly the newest one in its finite test bank. Direct modular arithmetic gives that witness as

    830844066280753740290752518400322793367016184651593732692413674633544921878

These counts describe distinct candidate failures, not exhausted catalogues. The rank-23 search retained a model missing 24 of 1,024 fixed training probes. That number has no coverage implication. In the eleven-prime unrestricted-phase run the logged completed calls spent 102.41 s solving SAT, 5.55 s encoding constraints and 0.36 s finding exact holes. The implementation hints the restored witness phases to the solver. A quantum oracle for detecting an uncovered word would evaluate each phase equality and negate their disjunction. These timings give no evidence of a practical advantage over the measured classical hole finder.

## Restart and independent replay

Run from this directory with Python 3, python-sat (CaDiCaL 1.9.5 and Glucose backends) and NumPy installed. The following commands resume the archived mathematical problems. Absolute paths in historical run metadata refer to their original working directory. The relative paths below are portable.

```sh
python3 prefix_sat.py --resume Runs/shifted8.json.gz --rounds 10000 --seconds 600
python3 prefix_incumbent.py --input Runs/base23.json.gz --output Runs/rank23.json.gz --integer-file Runs/integer_bank_final.json.gz --rounds 400 --seconds 600
python3 prefix_incumbent.py --input Runs/base24.json.gz --output Runs/rank24.json.gz --integer-file Runs/integer_bank_final.json.gz --rounds 400 --seconds 600
python3 harrington_cegis.py --extend 620 --extension-min 20001 --output Runs/beyond20000.json.gz --integer-file Runs/integer_bank_final.json.gz --rounds 400 --seconds 600
python3 release_unaries.py --output Runs/released24.json.gz --rounds 400 --seconds 600
python3 restart_check.py
python3 audit_checkpoint.py
python3 fresh_coordinate_bound.py
drat-trim Runs/control.cnf Runs/control.drat
PYTHONPATH=.. python3 Review/vivian_mixed_pair.py
```

Run the audit on the archived inputs before extending them. Resume reconstructs all clauses from the complete observations and saved catalogue. Search checkpoints contain the most recent candidate, a separately scored incumbent where applicable, seeds, parameters and a pending-exact-check flag. Each accepted model and each exact counterexample is committed by writing and syncing a temporary file, renaming it and syncing the directory. The supervisor handles timeouts, SIGINT and SIGTERM even inside a native SAT call. The interruption test sent SIGTERM after six rounds, recovered all 49 accumulated constraints, ran three further rounds and directly checked the next model against every old constraint. This restores the same mathematical problem. The solver's internal learned clauses are rebuilt.

Cross-catalogue import keeps the source checkpoint and its hash, lifts each labelled old observation to a CRT representative, then decodes the integer in the new prime/height schema. This provides a necessary point in the new search. A changed alphabet can split one former word into many, so a single representative does not stand for all its extensions. Concrete integers from prior runs are carried separately. The original per-root lift can turn a genuine atom hole into an actual escaping integer by enforcing residue −1 at each auxiliary prime. The released-unary branch started with 3,471 distinct integers. The newest bank contains 3,561 and can be rebuilt with `python3 collect_witnesses.py --output Runs/integer_bank_latest.json.gz`. The old bounded runs that never saved their observations cannot be reconstructed from a round count.

The remaining constructive obstacle is a coordinated change of the old-only phases or a different distribution of small-prime patterns that can close every residual fibre. The first four eligible fresh primes already put the simple product-measure bound above one. On the unrestricted proof side, the mixed-15 argument still allows the disjoint 3/9 configuration and covers carrying many mixed moduli. In the no-7 branch the next lemma is to bound the mass of large-prime classes on the two normalized heads modulo 45, retaining which low residues survived. The sharp examples exclude any increase in the uniform head-density lower bounds. An exploratory phase-sensitive envelope on the surviving residues modulo 45 also remained too large in both orbits. The [subset-envelope experiment](Review/ORBIT_ENVELOPE.md) preserves the computation. Lean separately checks affine normalization on the block modulo 45, together with the two scalar head inequalities. The previous literature and priority audit, including the limited July 2026 LCM bound and failed full-proof claims, is linked below. No priority for the unrestricted problem is asserted. [Literature audit](../README.md) · [Claims ledger](https://erdosproblems.ai/wiki/problems/covering_systems/E0007/claims)

Evan Tait commissioned the investigation for Conjecture Killers. Mabel carried out the search and the head and tail arguments with independent count and CRT-lift review. Vivian contributed the separated fresh-prime block argument and the earlier rank-20 counterexample. The distortion method is due to the authors cited in the mathematical notes. Priority for the new applications remains provisional.
