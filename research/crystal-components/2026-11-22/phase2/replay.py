"""Replay only the exchange continuation against the pinned predecessor modules."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

HERE=Path(__file__).resolve().parent
BASE=HERE.parent
PROOF=HERE/"proof"
LOGS=HERE/"logs"
LOGS.mkdir(exist_ok=True)
UNITS=("Cells","ThreeSupport","Fiber","Elimination","Separation","UnitSlice","WeakFamily","AxisResidues","Extremal","SuccessorSupport")
allowed={"propext","Classical.choice","Quot.sound"}
pin="0df444a360eaa60ab8c11dca51a86af692955474"
cache=BASE.parent.parent/"find-the-newest-message-in-my"/"work"
parser=argparse.ArgumentParser()
parser.add_argument("--unit",choices=UNITS)
parser.add_argument("--rebuild-base",action="store_true",
                    help="Compile historical sources into phase2/base-build without changing historical receipts")
parser.add_argument("--resume",action="store_true",help="Reuse the verified prefix with matching inputs and objects")
parser.add_argument("--mathlib",type=Path,default=os.environ.get("CRYSTAL_MATHLIB",cache/"mathlib4"))
parser.add_argument("--lean",type=Path,default=os.environ.get("CRYSTAL_LEAN",cache/"elan/toolchains/leanprover--lean4---v4.33.1/bin/lean.exe"))
args=parser.parse_args()
mathlib=args.mathlib.resolve()
lean=args.lean.resolve()
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def check_output(argv):
    return subprocess.check_output(argv,encoding="utf8",errors="replace").strip()
version=check_output([lean,"--version"])
assert "4.33.1," in version,version
rev=(mathlib/".git/HEAD").read_text().strip()
if rev.startswith("ref: "):rev=(mathlib/".git"/rev[5:]).read_text().strip()
assert rev==pin,rev
base_hashes=json.loads((HERE/"predecessor.json").read_text())["source_hashes"]
for path,expected in base_hashes.items():assert digest(BASE/path)==expected,path
historical=("Upstream","Crystal","Five","Transfer")
base_lib=BASE/"proof"
prepare_base=args.rebuild_base or not all((base_lib/(u+".olean")).is_file() for u in historical)
if prepare_base:
    base_lib=HERE/"base-build"
    base_lib.mkdir(exist_ok=True)
deps=[PROOF,base_lib,mathlib/".lake/build/lib/lean"]
deps.extend(p/".lake/build/lib/lean" for p in sorted((mathlib/".lake/packages").iterdir()) if p.is_dir())
env={**os.environ,"LEAN_PATH":os.pathsep.join(str(p) for p in deps),"LEAN_NUM_THREADS":"1"}
units=(args.unit,) if args.unit else UNITS
run={"version":version,"mathlib":rev,"units":{},"commands":[]}
def save_record(path,data):
    scratch=path.with_suffix(".tmp")
    with scratch.open("w",encoding="utf8") as stream:
        json.dump(data,stream,indent=2)
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(scratch,path)
def call(argv,seconds,cwd=PROOF):
    start=time.monotonic()
    result=subprocess.run(argv,cwd=cwd,env=env,capture_output=True,encoding="utf8",errors="replace",timeout=seconds)
    output=result.stdout+result.stderr
    run["commands"].append(dict(argv=[str(x) for x in argv],cwd=str(cwd),exit=result.returncode,seconds=time.monotonic()-start,output=output))
    print(output,flush=True)
    if result.returncode:
        save_record(LOGS/"build-incomplete.json",run)
        raise SystemExit(result.returncode)
    return output
checker=lean.with_name("leanchecker"+lean.suffix)
if prepare_base:
    for u in historical:
        (base_lib/(u+".lean")).write_bytes((BASE/"proof"/(u+".lean")).read_bytes())
        call([lean,"-j1","-M2048","-T1500000","-o",u+".olean",u+".lean"],450,base_lib)
    call([checker,"-v",*historical],600,base_lib)
run["historical_objects"]={u:digest(base_lib/(u+".olean")) for u in historical}
cached={}
if args.resume and not args.unit:
    candidates=[]
    for filename in ("verified.json","progress.json","build-incomplete.json"):
        path=LOGS/filename
        if not path.exists():continue
        old=json.loads(path.read_text(encoding="utf8"))
        if (old.get("version"),old.get("mathlib"),old.get("historical_objects")) != (version,rev,run["historical_objects"]):continue
        prefix=[]
        for u in UNITS:
            receipt=old.get("units",{}).get(u,{})
            obj=PROOF/(u+".olean")
            if not obj.is_file() or (digest(PROOF/(u+".lean")),digest(obj)) != (receipt.get("source_sha256"),receipt.get("object_sha256")):break
            prefix.append(u)
        candidates.append((len(prefix),prefix,old))
    if candidates:
        _,prefix,old=max(candidates,key=lambda c:c[0])
        cached={u:old["units"][u] for u in prefix}
        for u in prefix:
            saved=next(cmd for cmd in old["commands"] if cmd["exit"]==0 and cmd["argv"][-1]==u+".lean")
            run["commands"].append(saved)
        run["reused_units"]=prefix
for unit in units:
    src=PROOF/(unit+".lean")
    expected=re.findall(r"^#print axioms (\S+)\s*$",src.read_text(encoding="utf8"),re.M)
    assert expected,unit
    if unit in cached:
        output=next(cmd["output"] for cmd in run["commands"] if cmd["argv"][-1]==unit+".lean")
        print("Verified checkpoint:",unit,flush=True)
    else:
        output=call([lean,"-j1","-M2048","-T1500000","-o",unit+".olean",unit+".lean"],450)
    found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", output)
    for wanted in expected:
        assert any(n.rsplit(".",1)[-1]==wanted.rsplit(".",1)[-1] for n,_ in found),wanted
    assert all(not ax or {a.strip() for a in ax.split(",")}<=allowed for _,ax in found),found
    run["units"][unit]={"source_sha256":digest(src),"object_sha256":digest(PROOF/(unit+".olean")),"axioms":dict(found)}
    if not args.unit:save_record(LOGS/"progress.json",run)
if not args.unit:
    out=call([checker,"-v",*units],600)
    for u in units:assert "replaying "+u in out,u
    save_record(LOGS/"verified.json",run)
else:
    (LOGS/(args.unit+"-elaboration.json")).write_text(json.dumps(run,indent=2),encoding="utf8")
print("Verification complete:",", ".join(units))
