# Crystal components — verified partial classification (research draft)

**Status:** The original uniqueness-of-crystal-components conjecture of Abrate, Barbero, Cerruti and Murru (2016) remains **unresolved**. No counterexample is claimed. This repository folder contains proof sources, audit receipts, and a report produced by the AI-assisted *Conjecture Killer* desktop research campaign on **November 22, 2026**. The proofs were reported to compile on Lean 4.33.1 / pinned Mathlib with a matching serialized Lean kernel replay; **an independent maintainer replay and a scholarly novelty audit are still pending**.

## Main reported result

Let `IsCrystalWithComponents n a b` be the original predicate from `arXiv:1601.03081` for odd `n` and a component pair `a,b>1` with `ab=n`. If `(n+1)/2` has **at most two distinct prime divisors**, then any crystal has `n=35` and its sole unordered component pair is `{5,7}`. In particular, all qualifying pairs are unique in this infinite family. The prime exponents are unbounded.

Mabel reports the main result as `CrystalCampaign.StageTwo.only35OfTwoPrimeHalfSuccessor`, with nearby `twoPrimeHalfSuccessorClassification` and `twoPrimeHalfSuccessorUniqueness`; see `phase2/proof/SuccessorSupport.lean` and `phase2/PROOF_LEDGER.md` for **the exact hypotheses and dependencies**, rather than relying on this prose summary.

This is **not** a proof of the full conjecture. No claim of priority or independent originality has been established. Other reported results include the four-cell factor-exchange normal form, a strict inequality excluding a region of possible collisions, and fixed-exchange arithmetic certificates.

## Navigating the sources

- `phase2/PROOF_LEDGER.md` — result-by-result statements, statuses, and failed routes.
- `phase2/proof/*.lean` — ten continuation proof modules, imported in the recorded order.
- `proof/*.lean` — four predecessor modules and the extracted original predicate (with the admitted uniqueness theorem excluded).
- `phase2/logs/verified.json` — saved compiler/kernel/axiom receipt, **not freshly rerun during this GitHub transfer**.
- `phase2/replay.py` — local verification script; requires pinned dependencies and the predecessor modules as described in `phase2/README.md`.
- `Crystal_Components_Phase_II_Report.pdf` — human-readable mathematical report with all embedded files removed from this public rendering.

The original source-only archive was extracted from an attachment embedded in Mabel's original report; relevant source bytes are preserved here, except the `phase2/README.md` workspace description, which was sanitized for publication. No credentials or workspace-private files were intentionally included.

## Reproduction and trust

Pinned formal-conjectures revision: `2207c54d0dbe960de591d280f997b195bf3f6e28`. Lean: `v4.33.1`. Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`. The supplied verification record reports the only axioms `propext`, `Classical.choice`, and `Quot.sound`. Verify this claim against the actual source and the original target statement before citing the theorem formally. The complete upstream repository has not been rebuilt in this transfer.

**Original paper:** [The Biharmonic Mean](https://arxiv.org/abs/1601.03081). **Original formal statement:** [Google DeepMind formal-conjectures pinned source](https://github.com/google-deepmind/formal-conjectures/blob/2207c54d0dbe960de591d280f997b195bf3f6e28/FormalConjectures/Arxiv/1601.03081/UniqueCrystalComponents.lean).

**Responsible publication note:** AI-generated formal claims need scope auditing, an independent replay, and a literature novelty check. This is a research disclosure, not a peer-reviewed paper.
