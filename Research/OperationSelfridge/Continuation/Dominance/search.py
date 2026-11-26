"""Mixed-phase coordinate search and complete-unary SAT with labelled product cuts."""
from argparse import ArgumentParser
from hashlib import sha256
from math import prod
from pathlib import Path
from random import Random
import sys

import numpy as np

from repair import HERE, Rows, pack, read, validate, word_codes, write
from unary_orbits import switch_orbit
from dominance import normalize_unaries, phase_count, surviving_alphabets
from prefix_sat import actual_witness, key
from release_unaries import refit
from SliceLearning.product_learning import PatternIndex, slice_batch


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def restored(source, repairs, base):
    out = list(source[base])
    for rec in repairs["records"]:
        if rec["base"] != base:
            continue
        for i, old, new in rec["changes"]:
            if rec["step"] == "unary":
                old, new = [old], [new]
            assert out[i] == old
            out[i] = new
    return out


def improve(ps, hs, slots, initial, words, sample_size, seed, sweeps):
    """Exact one-slot best response for the finite weighted sample, with fixed unaries."""
    alph, _ = surviving_alphabets(ps, hs, slots, initial)
    rng = np.random.default_rng(seed)
    probes = np.column_stack([rng.choice(axis, sample_size) for axis in alph])
    rows = Rows(ps, hs, np.vstack([word_codes(ps, words), probes]))
    hard = len(words)
    phases = list(initial)
    incidence = np.zeros(rows.size, dtype=np.int32)
    for slot, phase in zip(slots, phases):
        if phase is not None:
            incidence += rows.hits(slot, phase)
    order = [i for i, slot in enumerate(slots) if len(slot) > 1]
    total_changes = 0
    for _ in range(sweeps):
        rng.shuffle(order)
        moves = 0
        for i in order:
            slot, old = slots[i], phases[i]
            old_hits = rows.hits(slot, old) if old is not None else np.zeros(rows.size, dtype=bool)
            # Temporarily delete this pattern. Only rows now at zero can add score.
            incidence -= old_hits
            target = np.flatnonzero(incidence == 0)
            if not len(target):
                incidence += old_hits
                continue
            dims = tuple(phase_count(ps[c], hs[c], e) for c, e in slot)
            labels = np.ravel_multi_index([rows.terms[tuple(t)][target] for t in slot], dims)
            unique, where = np.unique(labels, return_inverse=True)
            hits = np.bincount(where)
            essential = target < hard
            # Radix rows.size+1 makes a hard observation dominate any sample difference.
            hits += (rows.size + 1) * np.bincount(where[essential], minlength=len(unique))
            k = hits.argmax()
            old_gain = int(np.count_nonzero(old_hits[target])) + (rows.size + 1) * int(np.count_nonzero(old_hits[target[essential]]))
            if hits[k] > old_gain:
                phases[i] = list(map(int, np.unravel_index(unique[k], dims)))
                incidence += rows.hits(slot, phases[i])
                moves += 1
            else:
                incidence += old_hits
        total_changes += moves
        if not moves:
            break
    return phases, total_changes, int((incidence[:hard] == 0).sum()), int((incidence[hard:] == 0).sum())


def run(args):
    src, rep = read(args.source), read(args.repairs)
    assert digest(args.source) == rep["source_sha256"]
    ps, hs, slots = src["primes"], src["heights"], src["slots"]
    if Path(args.output).exists():
        state = read(args.output)
        assert state["source_sha256"] == digest(args.source) and state["repairs_sha256"] == digest(args.repairs)
    else:
        state = dict(version="dominance-search-1", source_sha256=digest(args.source), repairs_sha256=digest(args.repairs),
                     primes=ps, heights=hs, slots=slots, parameters=dict(seed=args.seed, sample=args.sample, sweeps=args.sweeps,
                     batch=args.batch, sat_period=args.sat_period), original_unaries=src["original_unaries"],
                     observations=rep["observations"], integers=rep["integers"], start_base="best_phases",
                     latest_phases=restored(src, rep, "best_phases"), proposals=[], status="initial")
        if args.orbit and args.sat_period:
            raise ValueError("Set --sat-period 0 to keep the canonical unary profile fixed")
        if args.orbit:
            state["canonical_orbit"] = args.orbit
            state["latest_phases"] = switch_orbit(ps,hs,slots,state["latest_phases"],args.orbit)
        if args.extra:
            extra = read(args.extra)
            if (extra["primes"], extra["heights"], extra["slots"]) != (ps, hs, slots):
                raise ValueError("Cross-alphabet import needs a separate certified transfer")
            state["extra_sha256"] = digest(args.extra)
            state["observations"] = list(dict.fromkeys(map(key, state["observations"] + extra["observations"])))
            state["integers"] = list(dict.fromkeys(state["integers"] + extra["integers"]))
            state["inherited_products"] = extra.get("inherited_products", []) + [rec["product"] for rec in extra["proposals"] if "product" in rec]
    cfg = state["parameters"]
    known = set(map(key, state["observations"]))
    ints = set(state["integers"])
    for _ in range(args.rounds):
        if state["status"] == "box_cover":
            break
        j = len(state["proposals"])
        phases = state["latest_phases"]
        seed = cfg["seed"] + 2*j
        record = dict(round=j, seed=seed)
        sat_period = cfg["sat_period"]
        if sat_period and j % sat_period == sat_period-1:
            working = dict(observations=state["observations"],original_unaries=state["original_unaries"],
                           parameters=dict(conflicts=12000))
            fitted, forced, status = refit(working, ps, hs, slots, phases, Random(seed), normalize=True)
            record.update(sat_status=status, forced_slot=forced)
            if fitted is not None:
                assert list(fitted[forced]) != state["original_unaries"][forced]
                assert not normalize_unaries(ps, hs, slots, fitted, lambda i, v:v[0])[1]
                phases = fitted
        phases, moves, missed, sample_misses = improve(ps, hs, slots, phases, state["observations"],
                                                      cfg["sample"], seed+1, cfg["sweeps"])
        assert not normalize_unaries(ps, hs, slots, phases, lambda i, v:v[0])[1]
        record.update(local_moves=moves, missed_constraints=missed, residual_sample_misses=sample_misses,
                      changes=[[i,old,new] for i,(old,new) in enumerate(zip(state["latest_phases"],phases))
                               if (tuple(old) if old is not None else None) != (tuple(new) if new is not None else None)])
        pats = [pack(slot, v) for slot, v in zip(slots, phases) if v is not None]
        validate(ps, hs, pats)
        index = PatternIndex(ps, hs, pats)
        # Check each inherited family against the union until a separating point is found.
        cut = None
        for previous in reversed(state["proposals"]):
            if "product" in previous:
                cut = index.hole(previous["product"])
                if cut is not None:
                    record["separated_product"] = previous["round"]
                    break
        if cut is None:
            for k, box in enumerate(state.get("inherited_products", [])):
                cut = index.hole(box)
                if cut is not None:
                    record["separated_inherited_product"] = k
                    break
        if cut is None:
            cut = index.hole(index.alph)
        if cut is None:
            if missed:
                raise AssertionError("A box cover must cover all observations")
            state["status"] = "box_cover"
        else:
            family = index.grow(cut)
            points = slice_batch(family, cut, cfg["batch"], seed)
            record.update(word=cut, product=family, product_size=str(prod(map(len,family))), batch=points)
            # A partially repaired iterate is explicitly labelled; its exact cuts stay valid.
            state["status"] = "candidate_rejected" if missed == 0 else "partial_repair_rejected"
            for w in points:
                number = str(actual_witness(w, ps, hs))
                if w not in known:
                    state["observations"].append(w)
                    known.add(w)
                if number not in ints:
                    state["integers"].append(number)
                    ints.add(number)
        state["latest_phases"] = phases
        state["proposals"].append(record)
        write(args.output, state)
        print(j, state["status"], "old misses", missed, "sample misses", sample_misses, "local moves", moves,
              "SAT",record.get("sat_status"),"bank", len(known), flush=True)


if __name__ == "__main__":
    p = ArgumentParser()
    p.add_argument("--source", default="Runs/released24.json.gz")
    p.add_argument("--repairs", default="Dominance/repairs.json.gz")
    p.add_argument("--output", default="Dominance/search.json.gz")
    p.add_argument("--orbit", choices=("sibling","third"), help="Canonicalize and if necessary switch the ternary unary orbit before fitting")
    p.add_argument("--extra", help="Import labelled observations, integers and products of an identical-schema search")
    p.add_argument("--rounds", type=int, default=6)
    p.add_argument("--sample", type=int, default=8192)
    p.add_argument("--sweeps", type=int, default=3)
    p.add_argument("--batch", type=int, default=48)
    p.add_argument("--seed", type=int, default=261144)
    p.add_argument("--sat-period", type=int, default=4)
    run(p.parse_args())
