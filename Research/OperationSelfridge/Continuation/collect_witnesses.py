"""Collect integer obligations without dropping their source checkpoints."""
import argparse
from pathlib import Path

from prefix_sat import actual_witness, read, write


def collect(folder, output):
    bank = set()
    sources = {}
    for path in sorted(folder.glob("*.json*")):
        if path.resolve() == output.resolve():
            continue
        data = read(path)
        if not isinstance(data, dict):
            continue
        values = set(map(int, data.get("integers", [])))
        values.update(map(int, data.get("harrington_integers", [])))
        values.update(map(int, data.get("integer_requirements", [])))
        values.update(map(int, data.get("holes", [])))
        if data.get("pending_obligation"):
            values.add(int(data["pending_obligation"]["integer"]))
        if data.get("schema") == "multi-pattern-rough-row-1":
            values.update(int(h["integer"]) for h in data["exact_holes"])
        elif data.get("version") in ("incumbent-1", "prefix-cegis-2"):
            cfg = data.get("config", data)
            for word in data["exact_holes"]:
                values.add(actual_witness(word, cfg["primes"], cfg["heights"]))
        if values:
            sources[path.name] = len(values)
            bank.update(values)
    write(output, dict(integers=list(map(str, sorted(bank))), source_counts=sources,
                       meaning="Permanent test integers. Each historical escape refers to its source generator and model."))
    print("distinct integer obligations", len(bank), sources)


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--folder", type=Path, default=Path("Runs"))
    p.add_argument("--output", type=Path, default=Path("Runs/integer_bank_final.json.gz"))
    a = p.parse_args()
    collect(a.folder, a.output)
