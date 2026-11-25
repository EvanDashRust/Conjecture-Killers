#!/usr/bin/env bash
set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
build_dir="$(mktemp -d)"
trap 'rm -rf -- "$build_dir"' EXIT
export LEAN_PATH="$build_dir"

lean --version
lean -o "$build_dir/Construction.olean" Construction.lean
lean -o "$build_dir/Checker.olean" Checker.lean
lean -o "$build_dir/Tables.olean" Tables.lean
lean -o "$build_dir/Proof.olean" Proof.lean
lean -o "$build_dir/ThreePattern.olean" ThreePattern.lean
lean -o "$build_dir/PatternCertificates.olean" PatternCertificates.lean
lean PatternOptimal.lean
lean -o "$build_dir/ShiftCounterexample.olean" ShiftCounterexample.lean
lean -o "$build_dir/NearStrips.olean" NearStrips.lean
lean TypeThree.lean
