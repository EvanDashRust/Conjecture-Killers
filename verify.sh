#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
# Publication launcher. Original historical clean build and audit are
# preserved in VERIFICATION_RECORD.md.
lean --version
lake --version
lake update
lake exe cache get
REV="$(git -C .lake/packages/mathlib rev-parse HEAD)"
test "$REV" = d13f23b723b8a846827a245b89c10fc7d3f11612
lake build
lake env lean Audit.lean
