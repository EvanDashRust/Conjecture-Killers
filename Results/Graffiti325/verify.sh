#!/usr/bin/env bash
set -euo pipefail

proof_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
revision=9097e2f90e66d2f6244209cb1c07f7120d17ec53

if [[ $# -gt 0 ]]; then
  source_dir="$(cd -- "$1" && pwd)"
else
  source_dir="$(mktemp -d)"
  trap 'rm -rf -- "$source_dir"' EXIT
  git -C "$source_dir" init --quiet
  git -C "$source_dir" fetch --quiet --depth 1 \
    https://github.com/google-deepmind/formal-conjectures.git "$revision"
  git -C "$source_dir" checkout --quiet --detach FETCH_HEAD
fi

cd -- "$source_dir"
if [[ "$(git rev-parse HEAD)" != "$revision" ]]; then
  printf 'Expected Formal Conjectures at %s\n' "$revision" >&2
  exit 1
fi

lake exe cache get \
  Mathlib.Analysis.Real.Sqrt \
  Mathlib.Combinatorics.SimpleGraph.Clique \
  Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite \
  Mathlib.Combinatorics.SimpleGraph.Finite \
  Mathlib.Order.CompletePartialOrder \
  Mathlib.Data.Multiset.Sort

lake build \
  +FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Degrees \
  +FormalConjecturesForMathlib.Combinatorics.SimpleGraph.WellTotallyDominated
lake env lean --version
lake env lean "$proof_dir/Proof.lean"
