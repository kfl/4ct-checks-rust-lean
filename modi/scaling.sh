#!/usr/bin/env bash
# Parallel wall-clock scaling of the Rust and Lean ports: sweep thread counts and
# report best-of-N wall-clock, with the (serial) C++ original as the reference.
# This answers goal (2): how much the ports' parallelisation buys on a real
# many-core Linux node (no macOS TLV / system-allocator artifacts).
#
#   apptainer exec ~/modi_images/hpc-notebook-*.sif modi/scaling.sh            # combine_rules
#   RUNS=5 THREADS="1 2 4 8 16 32 64" apptainer exec ~/modi_images/hpc-notebook-*.sif modi/scaling.sh
#
# NOTE: combine_rules is light + partly I/O-bound, so its scaling plateaus early.
# For a representative *compute* scaling curve, point WORKLOAD at a check_* phase
# once the cartwheel data is staged (see modi/README.md / run_full.sh).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
LIBDIR="$(cat "$ROOT/.lean_libdir" 2>/dev/null || dirname "$(find /root/.elan "${HOME:-/root}/.elan" -name 'libleanshared*' 2>/dev/null | head -1)" 2>/dev/null || true)"
[ -n "$LIBDIR" ] && export LD_LIBRARY_PATH="$LIBDIR:${LD_LIBRARY_PATH:-}"

CPP="$(dirname "$ROOT")/computer-checks/build/src/main"   # sibling C++ repo
RUST="$ROOT/rust_port/target/release/main"
LEAN="$ROOT/lean4_port/.lake/build/bin/main"
R="$ROOT/rust_port/discharging-rules/R"
C="$ROOT/rust_port/reducible-configurations/D"

OUT="$(mktemp -d)"; trap 'rm -rf "$OUT"' EXIT
ARGS=(--combine_rules -R "$R" -C "$C" -o "$OUT")   # the measured workload

RUNS="${RUNS:-3}"
# `nproc` can mis-report inside SLURM/containers (returns 2 on a 128-core MODI node);
# prefer SLURM's allocated count, then the hardware count, then nproc.
NP="${SLURM_CPUS_ON_NODE:-$(nproc --all 2>/dev/null || nproc)}"
THREADS="${THREADS:-}"
if [ -z "$THREADS" ]; then for t in 1 2 4 8 16 32 64 128; do [ "$t" -le "$NP" ] && THREADS="$THREADS $t"; done; fi

# best <env...> -- <cmd...>  -> min wall-clock (s) over RUNS
best() {
  local min=""
  for _ in $(seq 1 "$RUNS"); do
    local t0 t1 e
    t0="$(date +%s.%N)"; "$@" >/dev/null 2>&1; t1="$(date +%s.%N)"
    e="$(awk "BEGIN{print $t1-$t0}")"
    min="$(awk -v e="$e" -v m="$min" 'BEGIN{print (m==""||e<m)?e:m}')"
  done
  echo "$min"
}

echo "## scaling on $(uname -sm), $NP cores, best of $RUNS runs, workload: combine_rules"
cpp=""
if [ -x "$CPP" ]; then
  cpp="$(best "$CPP" "${ARGS[@]}")"
  printf '## C++ (serial reference): %.3fs\n\n' "$cpp"
else
  echo "## C++ reference not built — Rust/Lean only"; echo
fi
printf '%-8s %10s %10s %12s %12s %10s\n' threads "Rust(s)" "Lean(s)" "Rust spdup" "Lean spdup" "R vs C++"

r1=""; l1=""
for t in $THREADS; do
  r="$(best env RAYON_NUM_THREADS="$t" "$RUST" "${ARGS[@]}")"
  l="$(best env LEAN_NUM_THREADS="$t" "$LEAN" "${ARGS[@]}")"
  [ -z "$r1" ] && r1="$r"; [ -z "$l1" ] && l1="$l"
  awk -v t="$t" -v r="$r" -v l="$l" -v r1="$r1" -v l1="$l1" -v cpp="$cpp" \
    'BEGIN{printf "%-8s %10.3f %10.3f %12.2f %12.2f %10s\n", t, r, l, r1/r, l1/l, (cpp==""?"-":sprintf("%.2f",cpp/r))}'
done
