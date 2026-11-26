"""Exact prefix-tree relabellings for the two normalized released rank-24 profiles."""


def path(p, h, mode, phase):
    leaf = ()
    if mode == h + 1:
        phase, d = divmod(phase, p - 1)
        leaf = (d,)
    digits = []
    for _ in range(min(mode, h)):
        phase, d = divmod(phase, p)
        digits.append(d)
    if phase:
        raise ValueError("Phase outside mode")
    return tuple(digits) + leaf


def encode(p, h, digits):
    n = sum(d * p**i for i,d in enumerate(digits[:h]))
    return n * (p - 1) + digits[h] if len(digits) == h+1 else n


def relabelling(p, h, specification):
    """Extend prescribed pairs of paths to permutations of the children at each node."""
    assigned = {}
    for old_path, new_path in specification:
        if len(old_path) != len(new_path):
            raise ValueError("Inconsistent path depths")
        for k, (u, v) in enumerate(zip(old_path, new_path)):
            perm = assigned.setdefault(old_path[:k], {})
            if (u in perm and perm[u] != v) or (u not in perm and v in perm.values()):
                raise ValueError("Prescribed paths have different branching structure")
            perm[u] = v
    for prefix, perm in assigned.items():
        radix = p - 1 if len(prefix) == h else p
        free_source = sorted(set(range(radix)) - perm.keys())
        free_target = sorted(set(range(radix)) - set(perm.values()))
        perm.update(zip(free_source, free_target))
    def image(digits):
        return tuple(assigned.get(digits[:k], {}).get(d, d) for k,d in enumerate(digits))
    return image


def canonicalize(ps, hs, slots, phases):
    if ps[:3] != [3,5,7] or hs != [2,1,1]+[0]*(len(ps)-3):
        raise ValueError("The two-profile classification uses these heights and primes")
    unaries = {(s[0][0], s[0][1]): v[0] for s,v in zip(slots,phases) if len(s)==1}
    a,b,v = (unaries[0,e] for e in (1,2,3))
    root = v//2
    if b%3==a or root%3==a or root==b:
        raise ValueError("Ternary unaries must be disjoint")
    orbit = "sibling" if root%3 == b%3 else "third"
    maps = []
    targets = [[0,1,8 if orbit=="sibling" else 4],[0,4],[0,6]]+[[0] for _ in ps[3:]]
    for c,(p,h) in enumerate(zip(ps,hs)):
        specs = [(path(p,h,e,unaries[c,e]),path(p,h,e,t)) for e,t in enumerate(targets[c],1)]
        transform = relabelling(p,h,specs)
        table = []
        for e in range(1,h+2):
            n = p**e if e<=h else p**h*(p-1)
            row = [encode(p,h,transform(path(p,h,e,k))) for k in range(n)]
            assert sorted(row)==list(range(n))
            table.append(row)
        maps.append(table)
    new = [None if v is None else [maps[c][e-1][a] for (c,e),a in zip(slot,v)]
           for slot,v in zip(slots,phases)]
    return orbit,new,maps


def switch_orbit(ps,hs,slots,phases,target):
    orbit, new, _ = canonicalize(ps,hs,slots,phases)
    if target not in ("sibling","third"):
        raise ValueError("Unknown ternary profile")
    if orbit != target:
        i=next(i for i,slot in enumerate(slots) if len(slot)==1 and tuple(slot[0])==(0,3))
        new[i]=[8 if target=="sibling" else 4]
    return new
