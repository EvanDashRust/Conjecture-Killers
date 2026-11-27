"""Check every local unary profile in the released catalogue by explicit atom permutations."""
from collections import Counter
from functools import lru_cache
from itertools import product
from math import prod
from unary_orbits import path, relabelling, encode


def project(p,h,atom,e):
    return atom if e==h+1 else (atom//(p-1)) % p**e


def visit(p,h):
    n=p**h*(p-1)
    counts=Counter()
    domains=[range(p**e) for e in range(1,h+1)]+[range(n)]
    for vals in product(*domains):
        if any(sum(project(p,h,a,e)==v for e,v in enumerate(vals,1))>1 for a in range(n)):
            continue
        if h==2:
            is_sibling=(vals[1]%p)==((vals[2]//(p-1))%p)
            label="sibling" if is_sibling else "third"
            target=(0,1,8 if is_sibling else 4)
        elif h==1:
            label="one"
            target=(0,p-1)
        else:
            label="one"
            target=(0,)
        trans=relabelling(p,h,[(path(p,h,e,v),path(p,h,e,t)) for e,(v,t) in enumerate(zip(vals,target),1)])
        leaves=[encode(p,h,trans(path(p,h,h+1,a))) for a in range(n)]
        assert sorted(leaves)==list(range(n))
        for e,t in enumerate(target,1):
            images={}
            for a,b in enumerate(leaves):
                v,w=project(p,h,a,e),project(p,h,b,e)
                assert images.setdefault(v,w)==w
            assert sorted(images.values())==list(domains[e-1])
            assert images[vals[e-1]]==t
        counts[label]+=1
    return dict(counts)


def partitions(items, maximum):
    """Unordered set partitions, ordered canonically by first occurrence."""
    if not items:
        yield ()
        return
    first, *rest = items
    for partition in partitions(rest, maximum):
        if len(partition) < maximum:
            yield ((first,),) + partition
        for i in range(len(partition)):
            group = (first,) + partition[i]
            yield (group,) + partition[:i] + partition[i+1:]


def orbit_count(p, height):
    @lru_cache(None)
    def count(i, lengths):
        if not lengths or lengths == (0,):
            return 1
        if 0 in lengths:
            return 0
        children = p if i < height else p-1
        return sum(prod(count(i+1,tuple(d-1 for d in block)) for block in groups)
                   for groups in partitions(lengths, children))
    return count(0,tuple(range(1,height+2)))


def ternary_height_three_signatures():
    markers = range(1,5)
    options = [tuple(path(3,3,e,v) for v in range(3**e if e<=3 else 54)) for e in markers]
    signatures = set()
    for paths in product(*options):
        if any(b[:len(a)]==a for i,a in enumerate(paths) for b in paths[i+1:]):
            continue
        signatures.add(tuple(next(i for i,(u,v) in enumerate(zip(a,b)) if u!=v)
                             for i,a in enumerate(paths) for b in paths[i+1:]))
    return len(signatures)


if __name__=="__main__":
    import gzip,json
    from pathlib import Path
    s=json.load(gzip.open(Path(__file__).resolve().parents[1]/"Runs/released24.json.gz"))
    total=1
    for p,h in zip(s["primes"],s["heights"]):
        count=visit(p,h)
        assert count==({"third":108,"sibling":72} if h==2 else {"one":p*(p-1)**2 if h==1 else p-1})
        total*=sum(count.values())
        print(p,h,count)
    print("All normalized full-product unary layouts",total)
    for p in (3,5,7):
        assert [orbit_count(p,h) for h in range(3)]==[1,1,2]
        print("Prime",p,"orbit counts at heights 0 through 6",[orbit_count(p,h) for h in range(7)])
    assert ternary_height_three_signatures()==orbit_count(3,3)==6
    print("Ternary height-three pairwise common-prefix matrices",ternary_height_three_signatures())
