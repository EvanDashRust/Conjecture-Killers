"""Independent checks and explicit CRT lift for finite prime-prefix certificates."""
from argparse import ArgumentParser
from itertools import product
import json
from math import isqrt, lcm, prod
from pathlib import Path


def is_prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))


def validate(primes, heights, patterns, odd=True):
    if len(primes) != len(heights) or len(set(primes)) != len(primes):
        raise ValueError("Coordinate primes must be distinct and paired with heights.")
    if not all(is_prime(p) and (not odd or p % 2) for p in primes):
        raise ValueError("Coordinate moduli must be primes of the specified parity.")
    if not all(h >= 0 for h in heights):
        raise ValueError("Heights must be nonnegative.")
    used = set()
    for pattern in patterns:
        if not pattern or sorted({i for i, _, _ in pattern}) != [i for i, _, _ in pattern]:
            raise ValueError("Patterns must fix a nonempty set of distinct coordinates.")
        shape = tuple((i, e) for i, e, _ in pattern)
        if shape in used:
            raise ValueError("A mode vector may be used at most once.")
        used.add(shape)
        for i,e,a in pattern:
            if not 0 <= i < len(primes):
                raise ValueError("Unknown coordinate.")
            p,h=primes[i],heights[i]
            if not 1 <= e <= h + 1:
                raise ValueError("Mode outside the permitted range.")
            limit = p**e if e<=h else p**h*(p-1)
            if not 0 <= a < limit:
                raise ValueError("Phase outside the permitted range.")


def matches(primes, heights, point, pattern):
    for i,mode,phase in pattern:
        p,h=primes[i],heights[i]
        root,digit=point[i]
        if mode==h+1:
            if phase != root*(p-1)+digit-1:
                return False
        elif root % (p**mode) != phase:
            return False
    return True


def verify_hole(data):
    primes,heights=data["primes"],data["heights"]
    patterns=data["pure"]+data["patterns"]
    validate(primes,heights,patterns)
    word=data["uncovered_atom_word"]
    if word is None or len(word)!=len(primes):
        raise ValueError("The certificate needs an explicit atom word.")
    for p,h,(root,digit) in zip(primes,heights,word):
        if not (0<=root<p**h and 1<=digit<p):
            raise ValueError("The witness atom is outside the full alphabet.")
    if data.get("terminal"):
        i,root,q=terminal_data(primes,heights,data["terminal"],odd=True)
        if word[i][0]==root:
            raise ValueError("The alleged hole is covered by the terminal root.")
    if any(matches(primes,heights,word,a) for a in patterns):
        raise ValueError("The proposed hole meets a pattern.")
    print(f"Verified an exact atom-word hole across {len(patterns)} patterns.")


def terminal_data(primes,heights,terminal,odd):
    index,root,q=terminal
    if not 0<=index<len(primes) or not 0<=root<primes[index]**heights[index]:
        raise ValueError("Invalid terminal root.")
    if q in primes or not is_prime(q) or (odd and q%2==0) or q>heights[index]+1:
        raise ValueError("Not enough distinct divisors for the terminal closure.")
    return index,root,q


def check_complete_small(primes,heights,patterns,max_states,terminal=None):
    count=prod(p**h*(p-1) for p,h in zip(primes,heights))
    if count>max_states:
        raise ValueError(f"{count} exact states exceed this exhaustive verifier's budget.")
    alphabets=[tuple(product(range(p**h),range(1,p))) for p,h in zip(primes,heights)]
    for word in product(*alphabets):
        if terminal and word[terminal[0]][0]==terminal[1]:
            continue
        if not any(matches(primes,heights,word,a) for a in patterns):
            raise ValueError(f"Exact hole: {word}")


def crt(pairs):
    modulus=prod(m for m,_ in pairs)
    x=0
    for m,r in pairs:
        partial=modulus//m
        x+=r*partial*pow(partial,-1,m)
    return modulus,x%modulus


def lifted_classes(primes,heights,patterns,*,max_states=1000000,odd=True,terminal=None):
    """Yield explicit (modulus,residue) pairs after exhaustive finite verification."""
    validate(primes,heights,patterns,odd=odd)
    if terminal:
        terminal=terminal_data(primes,heights,terminal,odd)
    check_complete_small(primes,heights,patterns,max_states,terminal)
    auxiliary=[]
    next_prime=max([terminal[2] if terminal else 2,*primes,*(h+1 for h in heights)])+1
    for p,h in zip(primes,heights):
        mapping=[]
        for r in range(p**h):
            while not is_prime(next_prime):
                next_prime+=1
            q=next_prime
            next_prime+=1
            mapping.append(q)
            yield q,0
            for j in range(1,q):
                yield crt([(q,j),(p**j,r)])
        auxiliary.append(mapping)
    for pattern in patterns:
        choices=[]
        for i,e,a in pattern:
            p,h=primes[i],heights[i]
            if e<=h:
                choices.append([(p**e,a)])
            else:
                r,d=divmod(a,p-1)
                d+=1
                q=auxiliary[i][r]
                choices.append([(p**(k+1),r+d*p**k) for k in range(h,q-1)])
        for factors in product(*choices):
            yield crt(factors)
    if terminal:
        index,root,q=terminal
        yield q,0
        for j in range(1,q):
            yield crt([(q,j),(primes[index]**j,root)])


def control():
    # At p=2 the two root groups are filled by distinct fixed and variable modes.
    p=[2]
    h=[1]
    template=[[(0,1,0)],[(0,2,1)]]
    actual=list(lifted_classes(p,h,template,odd=False))
    assert len({m for m,a in actual})==len(actual)
    L=lcm(*(m for m,a in actual))
    assert all(any(x%m==a for m,a in actual) for x in range(L))
    print(f"Even positive control: {len(actual)} distinct classes cover all {L} residues.")
    try:
        list(lifted_classes(p,h,template[:1],odd=False))
    except ValueError as error:
        assert str(error).startswith("Exact hole")
    else:
        raise AssertionError("Removing the second pattern should fail coverage.")


if __name__=="__main__":
    parser=ArgumentParser()
    parser.add_argument("candidate",nargs="?")
    args=parser.parse_args()
    control()
    if args.candidate:
        verify_hole(json.loads(Path(args.candidate).read_text()))
