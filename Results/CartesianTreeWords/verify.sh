#!/usr/bin/env bash
set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
build_dir="$(mktemp -d)"
trap 'rm -rf -- "$build_dir"' EXIT
export LEAN_PATH="$build_dir"

lean --version
lean -o "$build_dir/Basic.olean" Basic.lean
lean -o "$build_dir/Certificates.olean" Certificates.lean
lean Result.lean
