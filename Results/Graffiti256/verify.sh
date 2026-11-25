#!/usr/bin/env bash
set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
build_dir="$(mktemp -d)"
trap 'rm -rf -- "$build_dir"' EXIT
mkdir -p "$build_dir/Graffiti255"

lean --version
lean --root=.. -o "$build_dir/Graffiti255/Counterexample.olean" ../Graffiti255/Counterexample.lean
LEAN_PATH="$build_dir" lean --root=.. Counterexample.lean
