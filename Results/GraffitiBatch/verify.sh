#!/usr/bin/env bash
set -euo pipefail

proofs="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
revision=fc4f59e577feb1a4956671bc04ac18aaaf8cd842
work="$(mktemp -d)"
trap 'rm -rf -- "$work"' EXIT

if [[ $# -gt 0 ]]; then
  mathlib="$(cd -- "$1" && pwd)"
else
  mathlib="$work/mathlib"
  git clone --quiet --depth 1 --branch v4.36.0 \
    https://github.com/leanprover-community/mathlib4.git "$mathlib"
fi
if [[ "$(git -C "$mathlib" rev-parse HEAD)" != "$revision" ]]; then
  printf 'Expected mathlib commit %s\n' "$revision" >&2
  exit 1
fi

cd -- "$mathlib"
lake exe cache get \
  Mathlib.Combinatorics.SimpleGraph.DegreeSum \
  Mathlib.Combinatorics.SimpleGraph.Metric \
  Mathlib.Combinatorics.SimpleGraph.Bipartite \
  Mathlib.Combinatorics.SimpleGraph.Star \
  Mathlib.Combinatorics.SimpleGraph.Matching
lake env lean --version

mkdir "$work/build"
lake env bash -s -- "$work/build" "$proofs" <<'LEAN'
set -euo pipefail
build="$1"
proofs="$2"
export LEAN_PATH="$build:$LEAN_PATH"
for module in Basic TwoDomination TotalDistance Critical IndependentDomination \
  MaximumDegreeDistance SpanningLeaves MatchingBound CoronaCounterexample; do
  lean -DwarningAsError=true --root="$proofs" -o "$build/$module.olean" "$proofs/$module.lean"
done
LEAN
