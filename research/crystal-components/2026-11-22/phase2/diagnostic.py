"""Bounded structural regression. The only new finite domain is eight predetermined orbit points."""
import hashlib
import json
from math import gcd
import msvcrt
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
LOGS = HERE / "logs"
BASE = HERE.parent
sys.path.insert(0, str(BASE / "diagnostics"))
import direct
import divisors
from host import working_set

def load(path):
    return json.loads(path.read_text(encoding="utf8"))

def save(path, data):
    raw = json.dumps(data, indent=2).encode("utf8")
    if len(raw) > 1_000_000:
        raise ValueError("Output exceeds 1 MB")
    tmp = path.with_suffix(".tmp")
    with tmp.open("wb") as stream:
        stream.write(raw)
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(tmp, path)

def sources():
    files = [Path(__file__), *(BASE / "diagnostics" / name for name in ("direct.py","divisors.py","host.py"))]
    return {file.name:hashlib.sha256(file.read_bytes()).hexdigest() for file in files}

def worker():
    start = time.monotonic()
    f = LOGS / "regression.json"
    state = load(f) if f.exists() else {
        "purpose":"Test the omitted successors on 17765 and the first eight positive R=5 orbit terms",
        "seed":None, "code":sources(), "next_case":0, "rows":[], "peak_bytes":0, "cpu_s":0,
        "wall_s":0, "b":1, "v":1, "status":"pending"}
    if state["code"] != sources():
        raise ValueError("Diagnostic source mismatch")
    old_cpu, old_wall = state["cpu_s"], state["wall_s"]
    for index in range(state["next_case"],9):
        if time.monotonic()-start>=590 or shutil.disk_usage(LOGS).free<1024**3:
            raise RuntimeError("Time or free-disk limit")
        if index==0:
            n,x,y,u,r=17765,11,19,5,17
        else:
            b,v=state["b"],state["v"]
            b,v=33*b+100*v,32*b+97*v
            assert 25*v*v==8*b*b+16*b*v+1
            state["b"],state["v"]=b,v
            x,y,u,r=2*b-v,2*b+5*v,1,5
            n=u*r*x*y
        factors=((u*x,r*y),(u*y,r*x))
        assert factors[0]!=factors[1] and set(factors[0])!=set(factors[1])
        k,l=((n+1)//sum(pair) for pair in factors)
        assert all(gcd(a,b)==1 and a*b==n and a>1 and b>1 for a,b in factors)
        assert all(q>=3 and q%2 and sum(pair)*q==n+1 for pair,q in zip(factors,(k,l)))
        rem=[sum(pair)%(q+1) for pair,q in zip(factors,(k,l))]
        assert all(rem) and all(direct.accepts(n,*pair)==divisors.accepts(n,*pair)==False for pair in factors)
        if index:
            assert (k,l)==(state["b"],state["b"]+2*state["v"])
            assert k*l%(4*r*r)==3
        state["rows"].append(dict(index=index,n=n,pairs=factors,quotients=[k,l],remainders=rem))
        state["peak_bytes"]=max(state["peak_bytes"],working_set())
        if state["peak_bytes"]>256*1024**2:
            raise RuntimeError("Memory cap")
        state.update(next_case=index+1,wall_s=old_wall+time.monotonic()-start,
                     cpu_s=old_cpu+time.process_time(),status="complete" if index==8 else "running")
        save(f,state)
    print("Regression complete",len(state["rows"]), "cases", flush=True)

def supervise():
    with (LOGS / "regression.lock").open("a+b") as lock:
        if lock.tell()==0:
            lock.write(b"0")
            lock.flush()
        lock.seek(0)
        msvcrt.locking(lock.fileno(),msvcrt.LK_NBLCK,1)
        dest=LOGS/"regression.json"
        if dest.exists() and load(dest)["status"]=="complete":
            assert load(dest)["code"]==sources()
            print("All nine checkpointed regression cases already complete.")
            return
        ledger=LOGS/"budget.json"
        original=load(BASE/"logs/budget.json")["reserved_cpu_s"]
        budget=load(ledger) if ledger.exists() else dict(predecessor_reserved_cpu_s=original,reserved_cpu_s=original,launches=[])
        assert original==3003 and budget["reserved_cpu_s"]+600<=7200
        budget["reserved_cpu_s"]+=600
        budget["launches"].append("17765-and-eight-R5-orbit-points")
        budget["remaining_cpu_s"]=7200-budget["reserved_cpu_s"]
        save(ledger,budget)
        start=time.monotonic()
        try:
            result=subprocess.run([sys.executable,__file__,"--worker"],timeout=590,check=False)
            rc=result.returncode
        except subprocess.TimeoutExpired:
            rc=124
        with (LOGS/"diagnostic-launches.jsonl").open("a",encoding="utf8") as out:
            out.write(json.dumps(dict(exit=rc,wall_s=time.monotonic()-start,
                supervisor_cpu_s=time.process_time(),child_deadline_s=590,worker_count=1))+"\n")
        raise SystemExit(rc)

if __name__=="__main__":
    if sys.argv[1:]==["--worker"]:
        worker()
    elif not sys.argv[1:]:
        supervise()
    else:
        raise SystemExit("Run python phase2/diagnostic.py")
