#!/usr/bin/env bash
# linenBench sweep over LEAN_NUM_THREADS on one node, with full provenance:
# commit, container image, lscpu, and the cgroup's Cpus_allowed_list. The
# 64->128 transition on MODI crosses from physical cores into SMT siblings,
# so the topology block is what makes the top of the sweep interpretable.
#
#   apptainer exec --bind ~/modi_mount ~/modi_images/hpc-notebook-*.sif modi/linen.sh
#   REPS=1 THREADS="64 96 128" apptainer exec ... modi/linen.sh     # quick scout
#
# linenBench itself prints uname, the LINEN_WORKERS/LEAN_NUM_THREADS env, the
# effective worker config, and per-configuration timings in microseconds.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
LIBDIR="$(cat "$ROOT/.lean_libdir" 2>/dev/null || dirname "$(find /root/.elan "${HOME:-/root}/.elan" -name 'libleanshared*' 2>/dev/null | head -1)" 2>/dev/null || true)"
[ -n "$LIBDIR" ] && export LD_LIBRARY_PATH="$LIBDIR:${LD_LIBRARY_PATH:-}"

BENCH="$ROOT/lean4_port/.lake/build/bin/linenBench"
[ -x "$BENCH" ] || { echo "linenBench not built: $BENCH (run lake build in lean4_port)"; exit 1; }

echo "## linenBench sweep"
echo "commit: $(git -C "$ROOT" rev-parse HEAD 2>/dev/null || echo unknown)$(git -C "$ROOT" diff --quiet 2>/dev/null || echo ' (dirty)')"
echo "image: ${APPTAINER_CONTAINER:-${SINGULARITY_CONTAINER:-unknown}}"
grep Cpus_allowed_list /proc/self/status || true
echo "## lscpu"
lscpu || true
echo "## /proc topology note: threads beyond 'Core(s) per socket' x 'Socket(s)' are SMT siblings"

REPS="${REPS:-3}"
FILTER="${FILTER:-}"
# `nproc` can mis-report inside SLURM/containers (returns 2 on a 128-core MODI
# node); prefer SLURM's allocated count, then the hardware count, then nproc.
NP="${SLURM_CPUS_ON_NODE:-$(nproc --all 2>/dev/null || nproc)}"
THREADS="${THREADS:-}"
if [ -z "$THREADS" ]; then
  for t in 1 2 4 8 16 32 64 96 128; do [ "$t" -le "$NP" ] && THREADS="$THREADS $t"; done
fi
echo "## reps: $REPS, threads swept:$( for t in $THREADS; do printf ' %s' "$t"; done )${FILTER:+, filter: $FILTER}"

for t in $THREADS; do
  echo
  echo "===== LEAN_NUM_THREADS=$t ====="
  env -u LINEN_WORKERS LEAN_NUM_THREADS="$t" "$BENCH" "$REPS" ${FILTER:+"$FILTER"}
done
