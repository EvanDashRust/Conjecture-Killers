#!/usr/bin/env bash
set -euo pipefail

proof_dir="$(cd -- "$(dirname -- "$0")" && pwd)"
revision=fc4f59e577feb1a4956671bc04ac18aaaf8cd842

if [[ $# -gt 0 ]]; then
  mathlib="$(cd -- "$1" && pwd)"
else
  mathlib="$(mktemp -d)"
  trap 'rm -rf -- "$mathlib"' EXIT
  git clone --quiet --depth 1 --branch v4.36.0 \
    https://github.com/leanprover-community/mathlib4.git "$mathlib"
fi

if [[ "$(git -C "$mathlib" rev-parse HEAD)" != "$revision" ]]; then
  printf 'Expected mathlib commit %s\n' "$revision" >&2
  exit 1
fi

cd -- "$mathlib"
lake exe cache get Mathlib.Analysis.SpecialFunctions.ExpDeriv \
  Mathlib.Analysis.Calculus.Deriv.Slope \
  Mathlib.LinearAlgebra.Matrix.Determinant.Basic \
  Mathlib.LinearAlgebra.Matrix.Notation \
  Mathlib.Tactic.FunProp \
  Mathlib.Tactic.FieldSimp \
  Mathlib.Tactic.FinCases \
  Mathlib.Tactic.Linarith \
  Mathlib.Tactic.NormNum \
  Mathlib.Tactic.Ring
lake env lean --version
lake env lean -DwarningAsError=true "$proof_dir/Proof.lean"
