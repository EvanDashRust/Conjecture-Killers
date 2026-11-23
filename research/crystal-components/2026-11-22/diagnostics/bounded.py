"""Serialize diagnostic jobs and enforce an independent hard wall deadline on Windows."""
import json
import msvcrt
from pathlib import Path
import subprocess
import sys
import time

root = Path(__file__).resolve().parent
if len(sys.argv) != 2 or sys.argv[1] not in {"pilot","structure"}:
    raise SystemExit("Usage: python bounded.py pilot|structure")
mode = sys.argv[1]
lock = root.parent/"logs"/"diagnostic.lock"
with lock.open("a+b") as gate:
    if gate.tell()==0:
        gate.write(b"0")
        gate.flush()
    gate.seek(0)
    msvcrt.locking(gate.fileno(),msvcrt.LK_NBLCK,1)
    start=time.monotonic()
    try:
        with (root.parent/"logs"/(mode+"-stdout.txt")).open("a",encoding="utf8") as out:
            child=subprocess.run([sys.executable,str(root/"run.py"),mode],timeout=595,
                                 stdout=out,stderr=subprocess.STDOUT)
        rc=child.returncode
    except subprocess.TimeoutExpired:
        rc=124
    receipt=dict(job=mode,exit_code=rc,wall_s=time.monotonic()-start,
                 supervisor_cpu_s=time.process_time(),worker_limit_s=595)
    dest=root.parent/"logs"/"launches.jsonl"
    with dest.open("a",encoding="utf8") as out:
        out.write(json.dumps(receipt)+"\n")
    print(receipt)
    sys.exit(rc)
