# Selection evidence

Frontier review date: November 22, 2026 (Eastern time). The board compares opportunities for an original mathematical result. “Open on available evidence” means the cited work leaves the exact claim unresolved and a targeted search found no verified resolution. It is a dated judgment about public evidence.

## Inventory and source control

The working input was the same-session `CONJECTURE_KILLER_RECON/`, checked against its saved archive and manifest. I loaded both complete master tables, matched their 1,911 statement IDs, and screened the JSONL descriptions, collection, scope markers, source pointers and disagreement flags across all rows. The input spans 16 collections. There are 1,120 problem grouping IDs, several of which are provisional file groups, and 303 statement rows with one or more flags. Twelve rows lack extracted statement text. A text pass surfaced 207 rows mentioning clues such as known cases, equivalences, conjecture numbering, explicit counterexamples, or finite reductions. Those clues drove follow-up, alongside manual review of promising themes in collections such as Green, arXiv, Erdős, MathOverflow, Papers and Other. Entries with sparse metadata still remained eligible. The 51 Terra leads, 72 competitor records and originals from the Davis catalogue were read as additional inputs. Every finalist was matched back to the master inventory and checked against the pinned Lean file and the available mathematical sources. The full-inventory pass was screening, and intensive status checks concentrated on finalists and significant exclusions.

| Source | Version or role |
|---|---|
| Formal Conjectures dashboard | 1,911 open statements on November 22. Published dataset hash `7e1119cf65a0ff537ebe2ba2c4c9551bf4ad417f7e73141d0a4be84fd2392bd8` from Phase I. Dashboard build commit unknown. |
| Formal Conjectures Git | `2207c54d0dbe960de591d280f997b195bf3f6e28`, rechecked against upstream HEAD. The pinned source specifies Lean `v4.33.1` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. |
| Davis solved-conjectures Git | `414c3aeef6c520cb12487180e9d20606660a8165`, rechecked against upstream HEAD. Reviewed alongside the site and its result-level status descriptions. |
| Erdős community YAML | Phase I pin `8e3d61bff616e6c6498d046eb6f0dd42cf4d9afe`. Original-problem claims and labels used as triage leads. |

[DeepMind dashboard](https://google-deepmind.github.io/formal-conjectures/) · [Pinned Lean sources](https://github.com/google-deepmind/formal-conjectures/tree/2207c54d0dbe960de591d280f997b195bf3f6e28) · [Davis tracker](https://itsdavis.com/solved-conjectures/) · [Pinned Davis catalogue](https://github.com/1337isnot1337/solved-conjectures/blob/414c3aeef6c520cb12487180e9d20606660a8165/CONTENTS.md) · [Erdős database snapshot](https://github.com/teorth/erdosproblems/tree/8e3d61bff616e6c6498d046eb6f0dd42cf4d9afe)

Each finalist's source dossier is in [SOL_TOP_TEN_TARGETS.md](SOL_TOP_TEN_TARGETS.md). Primary papers or original problem posts establish scope. A version of record supports published partials. A preprint may support the frontier and document a claim. A result-provider's proof, Lean log, or certificate is recorded as reported until independently replayed. MathOverflow and catalogue hits led to source artifacts. No kernel replay or new resolving computation was performed during selection. Source comparison was by inspection, and bridges flagged in the dossiers remain research work. Formal readiness grades describe the fixed statement and its verification path.

## Ranking model and sensitivity

Dimensions are integer editorial grades from 1 through 5. Grade 3 is viable with substantial caveats, 4 is favorable, and 5 is unusually favorable within this slate. Grade 2 signals a clear disadvantage. Significance measures the value of fully resolving the exact question. Tractability measures the quality of mathematical routes to resolution, including their unbounded gaps. Lean readiness scores definitions, fidelity and verification burden. Computational leverage measures the ability to discriminate between hypotheses or obtain witnesses. Novelty scores the remaining intellectual opportunity after accounting for active competition. Resource efficiency concerns the first informative work and its scaling risk. These grades express judgment and carry no probabilistic interpretation.

The baseline is `(25S + 25T + 15L + 15A + 10N + 10R)/5`. The table recomputes scores with the grades held fixed and dimensions in the same order. Ties are shown explicitly. CSV records the scores and ranks using competition ranking for ties.

| Scenario | Weights S/T/L/A/N/R | Leading order |
|---|---|---|
| Baseline | 25/25/15/15/10/10 | Minimum modulus and prescribed differences tied at 84, unfair polynomial 81, stable matching 80 |
| Significance emphasized | 40/20/10/10/10/10 | Prescribed differences 86, minimum modulus 82, unfair polynomial / weak tiling / Bondy tied at 80 |
| Fast feedback and limited resources | 15/30/15/15/5/20 | Minimum modulus 85, stable matching 84, prescribed differences and unfair polynomial tied at 82 |
| Lean readiness emphasized | 15/20/30/15/10/10 | Minimum modulus 87, prescribed differences 86, stable matching 82 |
| Novelty and competition emphasized | 20/20/10/15/25/10 | Stable matching 81, minimum modulus and prescribed differences tied at 80 |

A one-grade change in a 25% dimension moves a candidate by five points. The top two tie in the baseline. The board breaks that tie in favor of the lower burden of independently certifying a decisive validity witness and the opportunity for a diagnostic search with exact finite controls. A credible new family of near-threshold constructions, an improved lower bound, or a convincing computational obstruction could reverse their order. The bottom half is roughly a tier. The stable matching candidate earns the fast-win designation because a scalable bad-profile construction could support a short self-contained paper, while the overall pick has a better verified-claim interface and stronger combined mathematical and computational motivation.

## Holds and exclusions that materially changed the board

| Candidate | Finding and resulting decision |
|---|---|
| TxGraffiti Conjecture 3 | A public claimant presents a specific 50-vertex cubic graph and reports independent domination 16 and minimum maximal matching 15. Exact-scope priority is occupied by a concrete claim. Hold for a separate replay and source-hypothesis check. [Claim and artifacts](https://github.com/ipitchford/txgraffiti-conjecture3-resolution) |
| Dean, case k=5 | The May 2026 status in Terra is superseded by Botsford's exact-scope preprint claim and computational certificates. Hold pending review of the general reductions and artifact coverage. [Preprint](https://doi.org/10.5281/zenodo.22182448) · [Supplement](https://doi.org/10.5281/zenodo.22167084) |
| Gerstenhaber, three commuting matrices | A November 21 Palomar record asserts a full result, with a pinned artifact. Hold for independent correspondence and assumption audit. The November 8 dimension-bound preprint is partial. The newer proof artifact explicitly includes positive characteristic and supplies Comparator metadata. Independent replay remains outstanding. [Exact-scope claim](https://open-research-index.vercel.app/r/palomar/PALOMAR-2026-11-21-000010) · [Pinned Lean solution](https://github.com/lin522026298/three-commuting-matrices/blob/54c3e27589c55fa18f8679ef01b1e30feb2a9915/Solution.lean) · [Bound preprint](https://arxiv.org/abs/2611.11550) |
| Hadamard, order 668 | Egan et al. verify the published construction data at order 668. The universal conjecture is a different target, with live competing partial work at 2396. [Verification preprint, v2](https://arxiv.org/abs/2610.27175v2) · [2396 work](https://github.com/1337isnot1337/solved-conjectures/tree/414c3aeef6c520cb12487180e9d20606660a8165/results/hadamard-2396) |
| Erdős 506 | October 12 Cambie–Paliy–Wrona paper reports a complete resolution including the finite gap. Excluded. [Paper](https://arxiv.org/abs/2610.18918) |
| Green 24 asymptotic affine variant | Public result and certification recorded in October. The original finite conjecture requires separate priority analysis. [Result](https://conjectures.io/results/4b04c9b9-323d-446c-84e1-65f9dd09231d) |
| Green 14, W(2;3,21) | October exact-value claim has a large computation with external checker and a conditional Lean result. Hold for scope and dependency review. [Claim](https://zenodo.org/records/23776306) · [Certificates](https://zenodo.org/records/23749222) |
| Packing 21 circles in a square | Published literature records the computer-assisted optimum of Nurmela and Östergård. Excluded despite the old dashboard label. [Published retrospective](https://doi.org/10.1007/s10898-021-01086-z) |
| Borsuk in dimension four | Still an attractive reserve. Current preprints report upper bound six and leave the 5-versus-6 question. Exact Euclidean and all-set transfer burden is high. [Chalmers](https://www.preprints.org/manuscript/202611.0339) · [Tolmachev](https://arxiv.org/abs/2611.16775) |
| Arctangent sums | Ono's 2026 sparsity theorem and its AxiomMath artifacts leave complete nonintegrality open. A first exact sweep verifies only a finite range, while the sparse exceptional indices are the core difficulty. Held below the top ten. [Ono](https://arxiv.org/abs/2607.05739) · [Formal partials](https://github.com/AxiomMath/TanArctan) |

Priority can change between this board and launch. Search the exact statement, equivalent formulations, author pages, newer manuscript versions and linked artifacts again before investing. Preserve the original question, each computational bound, exact machine-check status, and each contributor's scope and attribution in the Phase III ledger.
