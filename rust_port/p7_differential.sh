#!/bin/bash
# P7 (cheap): differential validation of the Rust port against the C++ binary on
# a SUBSET of the real data. Runs combine_rules (Lemma A.1 / A.2) for both
# binaries and byte-diffs the output files. Seconds of compute.
#
# Covers, end-to-end on real data: rule + configuration parsing, the combine
# pipeline (free_homomorphism), the reducible-configuration blocking path
# (blocked_by_reducible_configuration / representative_degree / contain_conf /
# homomorphism), and byte-exact output formatting. The cartwheel enumeration
# engine and check drivers are covered instead by the ported unit tests
# (`cargo test`), which are exact-equality oracles against the C++ test suite.
#
# Usage: ./p7_differential.sh [NRULES]   (default 8)
set -euo pipefail
cd "$(dirname "$0")"

NRULES="${1:-8}"
CPP="${CPP:-../build/src/main}"
RUST="${RUST:-target/release/main}"

[ -x "$CPP" ] || { echo "C++ oracle not found at $CPP — build it: cmake --build ../build"; exit 1; }

# Fetch the data repos (shallow) if missing.
[ -d discharging-rules ] || git clone --depth 1 https://github.com/near-linear-4ct/discharging-rules.git
[ -d reducible-configurations ] || git clone --depth 1 https://github.com/near-linear-4ct/reducible-configurations.git

cargo build --release --quiet

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
mkdir -p "$WORK/R" "$WORK/empty" "$WORK/cpp_a1" "$WORK/rust_a1" "$WORK/cpp_a2" "$WORK/rust_a2"
for f in $(ls discharging-rules/R | sort | head -"$NRULES"); do cp "discharging-rules/R/$f" "$WORK/R/"; done

run_diff() { # label outdir_cpp outdir_rust  <args...>
    local label="$1" cpp_out="$2" rust_out="$3"; shift 3
    "$CPP"  "$@" -o "$cpp_out"  >/dev/null 2>&1
    "$RUST" "$@" -o "$rust_out" >/dev/null 2>&1
    if diff -r "$cpp_out" "$rust_out" >/dev/null; then
        echo "$label: IDENTICAL ($(ls "$cpp_out" | wc -l | tr -d ' ') files)"
    else
        echo "$label: DIFFERENCES FOUND"; diff -r "$cpp_out" "$rust_out" | head; exit 1
    fi
}

echo "== P7 differential ($NRULES rules) =="
run_diff "A.1 (empty C)"     "$WORK/cpp_a1" "$WORK/rust_a1" --combine_rules -R "$WORK/R" -C "$WORK/empty"
run_diff "A.2 (real configs)" "$WORK/cpp_a2" "$WORK/rust_a2" --combine_rules -R "$WORK/R" -C reducible-configurations/D
echo "All differential checks passed."
