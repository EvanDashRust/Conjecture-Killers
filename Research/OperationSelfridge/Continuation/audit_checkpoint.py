"""Replay last-candidate counterexamples directly from the archived phase arrays."""
from pathlib import Path

from prefix_lift import matches, validate
from prefix_sat import catalogue, read, key
from prefix_incumbent import pack


def audit(path):
    s=read(path)
    if "classes" in s:
        classes=s["classes"]
        assert len(classes)==len({m for m,r in classes})
        assert all(m>1 and m%2 and 0<=r<m for m,r in classes)
        holes=set(s["holes"])
        assert holes.issubset(s["integers"])
        missed=[x for x in s["integers"] if not any(int(x)%m==r for m,r in classes)]
        assert s["status"]=="exact_hole" and missed==[s["holes"][-1]]
        return f"{len(classes)} distinct odd classes; exact final integer {missed[0]}"
    if s.get("version")=="incumbent-1":
        ps,hs=s["primes"],s["heights"]
        pats=[pack(slot,v) for slot,v in zip(s["slots"],s["latest_phases"]) if v is not None]
        validate(ps,hs,s["pure"]+pats)
        missing=[w for w in s["observations"] if not any(matches(ps,hs,w,p) for p in pats+s["pure"])]
        assert s["status"]=="exact_hole" and missing==[s["exact_holes"][-1]]
        return f"{len(s['observations'])} observations, only final labelled witness escapes"
    if s.get("version")=="prefix-cegis-2":
        cfg=s["config"]
        alph,pure,slots=catalogue(cfg)
        ps,hs=cfg["primes"],cfg["heights"]
        validate(ps,hs,pure+s["latest"])
        assert len(slots)==s["slot_count"] and len(s["latest"])==len(slots)
        actual=set(map(key,s["observations"]))
        assert set(map(key,s["exact_holes"]))<=actual
        if s["pending"]:
            check=lambda w:any(matches(ps,hs,w,p) for p in s["latest"]+pure)
            assert all(check(w) for w in s["observations"])
        elif s["exact_holes"]:
            assert not any(matches(ps,hs,s["exact_holes"][-1],p) for p in s["latest"]+pure)
        return f"{len(actual)} constraints, final phase-model check passed"
    return None


if __name__=="__main__":
    for path in sorted(Path("Runs").glob("*.json.gz")):
        result=audit(path)
        if result:
            print(path.name,result)
