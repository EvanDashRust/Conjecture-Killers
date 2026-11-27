"""Re-encode a finite UNSAT claim and check its DRAT proof with an external program."""
import argparse
from itertools import product
from pathlib import Path
import subprocess

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver
from prefix_sat import catalogue, read
from prefix_box import value


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("checkpoint")
    parser.add_argument("--drat-trim", required=True)
    parser.add_argument("--base", required=True)
    args = parser.parse_args()
    state = read(args.checkpoint)
    assert state["status"] == "unsat_finite_constraints"
    cfg = state["config"]
    primes, heights = cfg["primes"], cfg["heights"]
    _, _, slots = catalogue(cfg)
    pool, cnf = IDPool(), CNF()
    choices = [set() for _ in slots]
    for word in state["observations"]:
        covered = []
        for i, slot in enumerate(slots):
            projection = tuple(value(primes[j], heights[j], word[j], e) for j,e in slot)
            phase = pool.id((i,projection))
            choices[i].add(phase)
            covered.append(phase)
        cnf.append(covered)
    for domain in choices:
        cnf.extend(CardEnc.atmost(sorted(domain), 1, vpool=pool, encoding=EncType.seqcounter))
    cnf_file, proof_file = args.base + ".cnf", args.base + ".drat"
    cnf.to_file(cnf_file)
    with Solver(name="glucose4", bootstrap_with=cnf.clauses, with_proof=True) as solver:
        assert solver.solve() is False
        proof = solver.get_proof()
        Path(proof_file).write_text("\n".join(proof or ["0"])+"\n")
    run = subprocess.run([args.drat_trim,cnf_file,proof_file], capture_output=True, text=True)
    assert "s VERIFIED" in run.stdout and run.returncode == 0, run.stdout+run.stderr
    print("Independent CNF and DRAT verified:", cnf.nv, "variables,", len(cnf.clauses), "clauses")


if __name__ == "__main__":
    main()
