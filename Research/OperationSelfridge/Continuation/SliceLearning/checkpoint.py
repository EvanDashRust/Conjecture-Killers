"""Build or replay the rank-24 product and repair certificates from exact inputs."""
import argparse
from functools import lru_cache
import gzip
from hashlib import sha256
from itertools import product
import json
from math import isqrt, prod
from pathlib import Path
from random import Random

from product_learning import PatternIndex, phase
from repair_distance import repair_test

HERE = Path(__file__).resolve().parent
DATA = HERE / 'rank24_products.json.gz'
SOURCE = HERE.parent / 'Runs/released24.json.gz'
REP = HERE.parent / 'Dominance/repairs.json.gz'
IDS = ('single_3', 'latest_mixed', 'scored_mixed')


def read(path):
    with gzip.open(path, 'rt') as f:
        return json.load(f)


def patterns_for(name):
    source = read(SOURCE)
    base = 'best_phases' if name == 'scored_mixed' else 'latest_phases'
    phases = source[base]
    if name == 'single_3':
        assert phases[2] == [12] and source['slots'][2] == [[0, 3]]
        phases[2] = [2]
    else:
        archive = read(REP)
        assert archive['source_sha256'] == sha256(SOURCE.read_bytes()).hexdigest()
        for row in archive['records']:
            if row['base'] != base:
                continue
            for j, old, new in row['changes']:
                if row['step'] == 'unary':
                    old, new = [old], [new]
                assert phases[j] == old
                phases[j] = new
    pats = [[(*a, v) for a, v in zip(slot, vals)] for slot, vals
            in zip(source['slots'], phases) if vals is not None]
    return source['primes'], source['heights'], pats


def corpus(index, high, seed):
    rng = Random(seed)
    holes, shadow = [], []
    while len(holes) < 512 or len(shadow) < 1024:
        w = tuple(rng.choice(a) for a in index.alph)
        active, permanent = index.all, high.all
        for i, atom in enumerate(w):
            active &= index.accept[i][atom]
            permanent &= high.accept[i][atom]
        if not active and len(holes) < 512:
            holes.append(w)
        elif active and not permanent and len(shadow) < 1024:
            shadow.append(w)
    return holes, shadow


@lru_cache(None)
def crt_terms(ps, hs):
    moduli = [p**(h+1) for p,h in zip(ps, hs)]
    q = max(*ps, *(h+1 for h in hs)) + 1
    aux = []
    for _ in range(sum(p**h for p,h in zip(ps, hs))):
        while any(q % d == 0 for d in range(2, isqrt(q)+1)):
            q += 1
        aux.append(q)
        q += 1
    moduli.append(prod(aux))
    period = prod(moduli)
    return period, tuple((period // m) * pow(period // m, -1, m) for m in moduli), moduli[-1]


def integer(w, ps, hs):
    period, terms, aux = crt_terms(tuple(ps), tuple(hs))
    x = (sum(t*(r+d*p**h) for (r,d),p,h,t in zip(w,ps,hs,terms)) - terms[-1]) % period
    assert x % aux == aux-1
    assert all(x % p**(h+1) == r+d*p**h for (r,d),p,h in zip(w,ps,hs))
    return str(x)


def direct(box, ps, hs, pats):
    assert len(box) == len(ps)
    for axis,p,h in zip(box,ps,hs):
        assert axis and len(set(map(tuple, axis))) == len(axis)
        assert all(0 <= r < p**h and 1 <= d < p for r,d in axis)
    possible = [{(e, phase(p,h,a,e)) for a in axis for e in range(1,h+2)}
                for axis,p,h in zip(box,ps,hs)]
    assert all(any((e,v) not in possible[i] for i,e,v in pat) for pat in pats)
    return prod(map(len, box))


def disjoint_boxes(index):
    rows = []
    rng = Random(4309)
    orders = [list(range(index.rank)), list(reversed(range(index.rank)))]
    orders += [rng.sample(range(index.rank),index.rank) for _ in range(8)]
    for head in index.alph[0]:
        word = index.hole(((head,),) + index.alph[1:])
        if word is None:
            continue
        choices = []
        for order in orders:
            # Restrict the first coordinate to a singleton for disjointness.
            # Process it last, so further head expansion cannot restrict other axes.
            box = index.grow(word, [i for i in order if i] + [0])
            choices.append(((head,),) + box[1:])
        box = max(choices, key=lambda b: prod(map(len,b)))
        rows.append(dict(seed=word, box=box, size=str(prod(map(len,box)))))
    return rows


def serial_digest(x):
    return sha256(json.dumps(x,separators=(',',':')).encode()).hexdigest()


def build():
    data = dict(version='released-rank24-product-repairs-1',
                source_sha256=sha256(SOURCE.read_bytes()).hexdigest(), seed=30, models={})
    for name in IDS:
        ps, hs, pats = patterns_for(name)
        data['coordinates'] = [{'prime':p,'height':h} for p,h in zip(ps,hs)]
        ix = PatternIndex(ps,hs,pats)
        holes, shadow = corpus(ix,PatternIndex(ps,hs,[p for p in pats if len(p)>2]),data['seed'])
        additive = 7 if name=='single_3' else 5
        upper,_ = repair_test(ps,hs,holes,additive)
        assert upper is not None
        boxes = disjoint_boxes(ix)
        for record in boxes:
            record['integer'] = integer(record['seed'],ps,hs)
        data['models'][name] = dict(pattern_sha256=serial_digest(pats), holes=holes,
            integers=[integer(w,ps,hs) for w in holes], shadow=shadow,
            additive=additive, upper=upper, products=boxes)
    tmp = DATA.with_suffix('.tmp')
    tmp.write_bytes(gzip.compress(json.dumps(data,separators=(',',':')).encode(),mtime=0))
    tmp.replace(DATA)


def verify(name,row,ps,hs,pats,edits):
    assert serial_digest(pats) == row['pattern_sha256']
    holes, shadow = row['holes'], row['shadow']
    assert len(set(map(str,holes)))==len(holes)==512 and len(shadow)==1024
    assert row['integers']==[integer(w,ps,hs) for w in holes]
    for w in holes:
        direct([(atom,) for atom in w], ps, hs, pats)
    seen = set()
    volume = 0
    for r in row['products']:
        box = r['box']
        assert len(box[0])==1
        head = tuple(box[0][0])
        assert head not in seen
        seen.add(head)
        assert all(atom in ax for atom,ax in zip(r['seed'],box))
        assert r['integer']==integer(r['seed'],ps,hs)
        size = direct(box,ps,hs,pats)
        assert str(size)==r['size']
        volume += size
    k = row['additive']
    answer,n = repair_test(ps,hs,holes,k-1)
    assert answer is None
    upper = row['upper']
    assert len(upper)==k and len(set(tuple((i,e) for i,e,v in p) for p in upper))==k
    for p in upper:
        assert p and all(0<=i<2 and 1<=e<=hs[i]+1 for i,e,_ in p)
    head = [p for p in pats if all(i < 2 for i,e,v in p)] + upper
    assert all(any(all(phase(ps[i],hs[i],w[i],e)==v for i,e,v in p) for p in head)
               for w in product(*PatternIndex(ps[:2],hs[:2],[]).alph))
    print(name, 'disjoint_products', len(seen), 'escaping_words',volume,
          'additive_optimum',k,'lower_bound_search_states',n,flush=True)
    answer,n = repair_test(ps,hs,holes+shadow,edits,original=pats)
    assert answer is None
    print(name,'edits_at_least',edits+1,'search_states',n,flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--build',action='store_true')
    parser.add_argument('--model',choices=IDS,action='append')
    args = parser.parse_args()
    if args.build:
        build()
    data = read(DATA)
    assert sha256(SOURCE.read_bytes()).hexdigest()==data['source_sha256']
    for name in args.model or IDS:
        ps,hs,pats=patterns_for(name)
        assert data['coordinates']==[{'prime':p,'height':h} for p,h in zip(ps,hs)]
        verify(name,data['models'][name],ps,hs,pats,{'single_3':9,'latest_mixed':8,'scored_mixed':8}[name])


if __name__=='__main__':
    main()
