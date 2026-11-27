"""Verify an explicit integer missing a saved family of actual odd congruences."""
from pathlib import Path
import json
import sys

parent = Path(__file__).resolve().parent.parent
checkpoint = parent if (parent / "harrington_seed.py").is_file() else parent / "selfridge3"
sys.path.insert(0, str(checkpoint))
from harrington_seed import seed

def check(path):
    data = json.loads(Path(path).read_text())
    original = list(seed())
    added = data["additions"]
    assert len(original) == data["seed_classes"]
    assert len(added) == data["added_classes"]
    used = set()
    witness = int(data["uncovered_integer"])
    for modulus, residue in original + added:
        assert modulus > 1 and modulus % 2 == 1
        assert 0 <= residue < modulus
        assert modulus not in used
        used.add(modulus)
        assert witness % modulus != residue
    print(f"Exact integer witness avoids all {len(used)} distinct odd classes.")
    print(witness)

if __name__ == "__main__":
    check(sys.argv[1])
