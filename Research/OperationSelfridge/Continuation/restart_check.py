"""Exercise actual SIGTERM, atomic persistence, and reconstruction of the same constraints."""
from pathlib import Path
import signal
import subprocess
import sys
from tempfile import TemporaryDirectory
from time import monotonic, sleep

from prefix_lift import matches
from prefix_sat import read

with TemporaryDirectory() as folder:
    checkpoint=Path(folder)/"restart.json.gz"
    entry=[sys.executable,str(Path(__file__).with_name("prefix_sat.py"))]
    child=subprocess.Popen(entry+["--rank","7","--free-unaries","--seconds","60","--rounds","50000",
                                  "--output",str(checkpoint)])
    try:
        deadline=monotonic()+30
        while not checkpoint.exists() or read(checkpoint)["completed"]<6:
            if child.poll() is not None or monotonic()>deadline:
                raise RuntimeError("Worker failed to reach the interruption test point")
            sleep(.01)
        child.send_signal(signal.SIGTERM)
        assert child.wait(10)==0
        before=read(checkpoint)
        assert before["status"]=="interrupted"
        subprocess.run(entry+["--resume",str(checkpoint),"--rounds","3","--seconds","30"],check=True)
        after=read(checkpoint)
        cfg=after["config"]
        assert cfg==before["config"] and after["slot_count"]==before["slot_count"]
        assert after["observations"][:len(before["observations"])]==before["observations"]
        assert after["completed"]>before["completed"]
        assert all(any(matches(cfg["primes"],cfg["heights"],word,p) for p in after["latest"])
                   for word in before["observations"])
        print("Verified interrupted reconstruction of",len(before["observations"]),"constraints")
    finally:
        if child.poll() is None:
            child.kill()
            child.wait()
