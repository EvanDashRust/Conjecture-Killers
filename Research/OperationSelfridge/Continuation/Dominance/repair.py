"""Normalize both rank-24 incumbents and reuse slots hidden behind pure cylinders."""
from argparse import ArgumentParser
import hashlib
from itertools import product
from pathlib import Path
from random import Random
import sys

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from prefix_box import exact_hole
from prefix_incumbent import pack
from prefix_lift import validate
from prefix_sat import actual_witness, key, read, write
from dominance import dead_mixed, normalize_unaries, phase_count, surviving_alphabets


class Rows:
    def __init__(self, primes, heights, codes):
        self.terms = {}
        self.size = codes.shape[0]
        for c, (p, h) in enumerate(zip(primes, heights)):
            for e in range(1, h + 1):
                self.terms[c, e] = (codes[:, c] // (p - 1)) % (p**e)
            self.terms[c, h + 1] = codes[:, c]

    def hits(self, slot, phase):
        return np.logical_and.reduce([self.terms[tuple(term)] == v for term, v in zip(slot, phase)])

    def missing(self, slots, phases):
        mask = np.ones(self.size, dtype=bool)
        for slot, phase in zip(slots, phases):
            if phase is not None:
                mask &= ~self.hits(slot, phase)
        return mask


def word_codes(primes, words):
    return np.array([[r * (p - 1) + d - 1 for p, (r, d) in zip(primes, w)] for w in words])


def sample_rows(primes, heights, alph, size, seed):
    rng = np.random.default_rng(seed)
    return Rows(primes, heights, np.column_stack([rng.choice(a, size) for a in alph]))


def improve_unaries(ps, hs, slots, phases, observed, samples):
    pending = [r.missing(slots, phases) for r in (observed, samples)]
    def choose(i, options):
        def gains(v):
            return tuple(np.count_nonzero(mask & rows.hits(slots[i], [v]))
                         for mask, rows in zip(pending, (observed, samples)))
        chosen = max(options, key=gains)
        for mask, rows in zip(pending, (observed, samples)):
            mask &= ~rows.hits(slots[i], [chosen])
        return chosen
    return normalize_unaries(ps, hs, slots, phases, choose)


def improve_mixed(ps, hs, slots, phases, observed, size, seed):
    """Only move wholly unary-covered patterns. Prefer missed real points, then samples."""
    phases = list(phases)
    alph, live = surviving_alphabets(ps, hs, slots, phases)
    samples = sample_rows(ps, hs, alph, size, seed)
    pending = [r.missing(slots, phases) for r in (observed, samples)]
    dead = dead_mixed(slots, phases, live)
    def max_mass(i):
        mass = 1
        for c, e in slots[i]:
            p, h = ps[c], hs[c]
            terms = [v if e == h + 1 else (v // (p - 1)) % (p**e) for v in alph[c]]
            mass *= np.bincount(terms).max() / len(terms)
        return mass
    # Largest surviving single-cell densities first. This ordering is heuristic.
    changes = []
    for i in sorted(dead, key=lambda i: -max_mass(i)):
        slot = slots[i]
        safe = [sorted(live[tuple(t)]) for t in slot]
        dims = [phase_count(ps[c], hs[c], e) for c, e in slot]
        # Each observed miss outside the unary slabs has a phase in this live product.
        best = None
        for rows, mask in zip((observed, samples), pending):
            if not mask.any():
                continue
            codes = np.ravel_multi_index([rows.terms[tuple(t)][mask] for t in slot], dims)
            values, counts = np.unique(codes, return_counts=True)
            leaders = values[counts == counts.max()]
            if best is not None:
                # Ties on old real witnesses are resolved by sample gain.
                codes = dict(zip(values, counts))
                best = [max(best, key=lambda v: codes.get(v, 0))]
                break
            best = list(leaders)
            if len(best) == 1:
                break
        if best is None:
            new = [s[0] for s in safe]
        else:
            new = list(map(int, np.unravel_index(best[0], dims)))
        assert all(v in options for v, options in zip(new, safe))
        changes.append([i, phases[i], new])
        phases[i] = new
        for rows, mask in zip((observed, samples), pending):
            mask &= ~rows.hits(slot, new)
    assert not dead_mixed(slots, phases, live)
    return phases, changes, int(pending[1].sum())


def run(args):
    source = read(args.source)
    ps, hs, slots = source["primes"], source["heights"], source["slots"]
    alph = [list(product(range(p**h), range(1, p))) for p, h in zip(ps, hs)]
    encoded = [list(range(len(a))) for a in alph]
    check = sample_rows(ps, hs, encoded, args.holdout, 11261951)
    guiding = sample_rows(ps, hs, encoded, args.sample, 11261952)
    oldrng = Random(source["seed"])
    oldprobes = [[oldrng.choice(a) for a in alph] for _ in range(source["parameters"]["probe_count"])]
    scored = Rows(ps, hs, word_codes(ps, oldprobes))
    original_words = list(source["observations"])
    all_words = list(original_words)
    all_integers = list(source["integers"])
    historical = Rows(ps, hs, word_codes(ps, original_words))
    records = []
    def record(base, step, phases, changes):
        patterns = [pack(s, v) for s, v in zip(slots, phases) if v is not None]
        validate(ps, hs, patterns)
        idx = exact_hole(alph, ps, hs, patterns)
        word = [a[k] for a, k in zip(alph, idx)] if idx is not None else None
        integer = str(actual_witness(word, ps, hs)) if word is not None else None
        if word is not None and key(word) not in set(map(key, all_words)):
            all_words.append(word)
        if integer is not None and integer not in all_integers:
            all_integers.append(integer)
        _, live = surviving_alphabets(ps, hs, slots, phases)
        row = dict(base=base, step=step, changes=changes, missed_original=int(historical.missing(slots, phases).sum()),
                   historical_probe_hits=scored.size-int(scored.missing(slots, phases).sum()),
                   holdout_misses=int(check.missing(slots, phases).sum()),
                   unary_hidden_mixed=len(dead_mixed(slots, phases, live)), word=word, integer=integer)
        records.append(row)
        print(base, step, {k:v for k,v in row.items() if k not in ("changes","word","integer")}, flush=True)
    for base in ("latest_phases", "best_phases"):
        old = source[base]
        record(base, "original", old, [])
        phases, moves = improve_unaries(ps, hs, slots, old, historical, guiding)
        record(base, "unary", phases, moves)
        observed = Rows(ps, hs, word_codes(ps, all_words))
        phases, moves, misses = improve_mixed(ps, hs, slots, phases, observed, args.sample, 11261953)
        record(base, "mixed", phases, moves)
        records[-1]["residual_training_misses"] = misses
    state = dict(version="dominance-repair-1",source=Path(args.source).name,
                 source_sha256=hashlib.sha256(Path(args.source).read_bytes()).hexdigest(),
                 primes=ps,heights=hs,sample=args.sample,holdout=args.holdout,records=records,
                 observations=all_words,integers=all_integers)
    write(args.output, state)


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("--source", default="Runs/released24.json.gz")
    parser.add_argument("--output", default="Dominance/repairs.json.gz")
    parser.add_argument("--sample", type=int, default=32768)
    parser.add_argument("--holdout", type=int, default=32768)
    run(parser.parse_args())
