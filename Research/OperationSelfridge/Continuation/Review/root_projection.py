"""Check exact fixed-root geometry of the archived rank-20 prefix candidate."""
from itertools import product
from math import prod
from fractions import Fraction
from pathlib import Path
import argparse
import hashlib
import json
from shared_lift import integer_hole, setup

def verify(candidate_path, evidence_path):
    raw=Path(candidate_path).read_bytes()
    data=json.loads(raw)
    evidence=json.loads(Path(evidence_path).read_text())
    if hashlib.sha256(raw).hexdigest()!=evidence["candidate_sha256"]:
        raise ValueError("Input differs from the certified candidate")
    primes,heights=data["primes"],data["heights"]
    assert list(zip(primes,heights))==[(v["prime"],v["height"]) for v in evidence["coordinates"]]
    patterns=data["pure"]+data["patterns"]
    setup(primes,heights,patterns,79)
    assert primes[:3]==[3,5,7] and heights==[2,1,1]+[0]*17
    words={tuple(w[0] for w in point[:3]): point for point in evidence["atom_words"]}
    assert len(words)==len(evidence["atom_words"])==73
    for word in words.values():
        integer_hole(primes,heights,patterns,79,word)
    small=[P for P in patterns if all(i<3 for i,e,a in P)]
    fixed=[P for P in small if all(e<=heights[i] for i,e,a in P)]
    fixed_unary=[P for P in fixed if len(P)==1]
    def match(pat,roots,digits):
        for i,e,a in pat:
            value=roots[i]%primes[i]**e if e<=heights[i] else roots[i]*(primes[i]-1)+digits[i]-1
            if value!=a:
                return False
        return True
    classes=[0]*4
    for roots in product(range(9),range(5),range(7)):
        if roots in words:
            classes[3]+=1
        elif any(match(P,roots,()) for P in fixed_unary):
            classes[0]+=1
        elif any(match(P,roots,()) for P in fixed):
            classes[1]+=1
        else:
            for digits in product(range(1,3),range(1,5),range(1,7)):
                assert any(match(P,roots,digits) for P in small)
            classes[2]+=1
    assert classes==[195,45,2,73]
    assert {prod(primes[i]**e for i,e,a in P) for P in fixed}=={
        d for d in range(2,316) if 315%d==0
    }
    # At k=h each variable pattern copy realizes numerical exponent h+1.
    # These core labels consume even the additional smooth-only divisors below.
    base_labels={prod(primes[i]**e for i,e,_ in pat) for pat in patterns}
    for p in primes:
        bound=315*p
        assert all(d in base_labels for d in range(2,bound+1) if bound%d==0)
    # In this particular root cylinder only the following old per-root
    # auxiliary classes survive beyond the single pure class for each q.
    from check_original import canonical_schematic
    word=words[8,4,5]
    extras=[]
    for (i,r),q in canonical_schematic(primes,heights,patterns).items():
        p,h=primes[i],heights[i]
        actual_root,digit=word[i]
        x=actual_root+digit*p**h
        count=sum((x-r)%p**j==0 for j in range(1,h+1))
        if count:
            extras.append((q,count))
    assert extras==[(89,1),(103,1),(113,2),(149,1),(179,1)]
    cost=sum(Fraction(10*count,7*q) for q,count in extras)
    assert cost+Fraction(922631528,10**9)<1
    print("Additional mass bound for (8,4,5):",cost)
    print("All 315 root triples verified:",classes,"(fixed unary, other fixed, local-digit cover, hole).")

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("candidate")
    p.add_argument("evidence")
    a=p.parse_args()
    verify(a.candidate,a.evidence)
