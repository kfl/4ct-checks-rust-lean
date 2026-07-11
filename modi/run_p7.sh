#!/usr/bin/env bash
# Cheap byte-identical correctness check: runs combine_rules (Lemma A.1 / A.2) for
# C++, Rust, and Lean and diffs the outputs. THE FIRST THING TO RUN on a MODI node
# — it's minutes, and it catches any cross-platform non-determinism before you
# commit a node to the multi-hour full run.
#
#   apptainer exec ~/modi_images/hpc-notebook-*.sif modi/run_p7.sh      # 8-rule subset (fastest)
#   apptainer exec ~/modi_images/hpc-notebook-*.sif modi/run_p7.sh 0    # 0 = all rules (a few minutes)
#
# Exits non-zero (and prints DIFFER) on any mismatch.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"          # repo root
NRULES="${1:-8}"                                   # 8-rule subset by default

# Make sure the Lean binary can find libleanshared (the build records its dir).
LIBDIR="$(cat "$ROOT/.lean_libdir" 2>/dev/null || true)"
if [ -z "$LIBDIR" ]; then
    LIBDIR="$(dirname "$(find /root/.elan "${HOME:-/root}/.elan" -name 'libleanshared*' 2>/dev/null | head -1)" 2>/dev/null || true)"
fi
[ -n "$LIBDIR" ] && export LD_LIBRARY_PATH="$LIBDIR:${LD_LIBRARY_PATH:-}"

# p7_differential.sh resolves its binaries relative to lean4_port; override here so
# the paths are anchored at the repo root. The C++ reference lives in the sibling
# `computer-checks` repo (the static binary is dropped at its build/src/main).
export CPP="${CPP:-$(dirname "$ROOT")/computer-checks/build/src/main}"
export RUST="${RUST:-$ROOT/rust_port/target/release/main}"
export LEAN="${LEAN:-$ROOT/lean4_port/.lake/build/bin/main}"
export DATA="${DATA:-$ROOT/rust_port}"

echo "## p7 differential on $(uname -sm), $(nproc) cores"
echo "##   C++ = $CPP"
echo "##   Rust= $RUST"
echo "##   Lean= $LEAN"
cd "$ROOT/lean4_port"
exec ./p7_differential.sh "$NRULES"
