"""Fixed diagnostic sample shared by all layouts. Values have no certificate role."""
from repair import HERE, read, sample_rows
from search import restored
from unary_orbits import switch_orbit

if __name__ == "__main__":
    s=read(HERE.parent/"Runs/released24.json.gz")
    rep=read(HERE/"repairs.json.gz")
    ps,hs,slots=s["primes"],s["heights"],s["slots"]
    sample=sample_rows(ps,hs,[range(p**h*(p-1)) for p,h in zip(ps,hs)],32768,11261951)
    for base in ("latest_phases","best_phases"):
        phase=list(s[base])
        for row in rep["records"]:
            if row["base"]!=base:
                continue
            for i,old,new in row["changes"]:
                phase[i]=[new] if row["step"]=="unary" else new
            missed=int(sample.missing(slots,phase).sum())
            assert missed==row["holdout_misses"]
            print(base,row["step"],missed,flush=True)
    for name in ("search","challenger","sibling"):
        st=read(HERE/f"{name}.json.gz")
        phase=restored(s,rep,st["start_base"])
        if "canonical_orbit" in st:
            phase=switch_orbit(ps,hs,slots,phase,st["canonical_orbit"])
        for j,row in enumerate(st["proposals"]):
            for i,old,new in row["changes"]:
                assert phase[i]==old
                phase[i]=new
            print(name,j,int(sample.missing(slots,phase).sum()),flush=True)
