"""Coverage-preserving repairs in the finite full-phase prefix catalogue."""


def phase_count(prime, height, mode):
    return prime**mode if mode <= height else prime**height * (prime - 1)


def cylinder_parent(prime, height, mode, phase, shallower):
    """The fixed ancestor of this phase at any strictly shallower mode."""
    root = phase if mode <= height else phase // (prime - 1)
    return root % prime**shallower


def unary_slots(slots):
    return sorted((coord, mode, i) for i, slot in enumerate(slots)
                  if len(slot) == 1 for coord, mode in slot)


def available_unary_phases(prime, height, mode, earlier):
    return [v for v in range(phase_count(prime, height, mode))
            if all(cylinder_parent(prime, height, mode, v, old_mode) != old_phase
                   for old_mode, old_phase in earlier)]


def normalize_unaries(primes, heights, slots, phases, choose, forbidden=None):
    """choose(i, candidates) selects a replacement; forbidden maps slot to one value."""
    forbidden = forbidden or {}
    result = list(phases)
    ancestors = [[] for _ in primes]
    moves = []
    for coord, mode, i in unary_slots(slots):
        old = result[i][0]
        if old == forbidden.get(i):
            raise ValueError("Starting layout violates the branch condition")
        legal = available_unary_phases(primes[coord], heights[coord], mode, ancestors[coord])
        if old not in legal:
            choices = [v for v in legal if v != forbidden.get(i)]
            new = choose(i, choices)
            if new not in choices:
                raise ValueError("Replacement outside the available phase set")
            moves.append((i, old, new))
            result[i] = [new]
        ancestors[coord].append((mode, result[i][0]))
    return result, moves


def surviving_alphabets(primes, heights, slots, phases):
    """Return live atoms as encoded variable phases, plus their live projections."""
    used = [set() for _ in primes]
    for c, e, i in unary_slots(slots):
        used[c].add((e, phases[i][0]))
    alph = []
    projections = {}
    for c, (p, h) in enumerate(zip(primes, heights)):
        def project(atom, mode):
            return atom if mode == h + 1 else (atom // (p - 1)) % (p**mode)
        live = [v for v in range(phase_count(p, h, h + 1))
                if all(project(v, mode) != value for mode, value in used[c])]
        alph.append(live)
        for e in range(1, h + 2):
            projections[c, e] = {project(v, e) for v in live}
    return alph, projections


def dead_mixed(slots, phases, projections):
    return [i for i, (slot, phase) in enumerate(zip(slots, phases))
            if len(slot) > 1 and phase is not None and
            any(v not in projections[tuple(literal)] for literal, v in zip(slot, phase))]
