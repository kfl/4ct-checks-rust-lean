#!/bin/bash
# P7: differential validation of the Lean port against BOTH oracles (the C++
# binary and the already-validated Rust port) on the real data. Runs combine_rules
# (Lemma A.1 / A.2) for all three binaries and byte-diffs the output files.
#
# Covers, end-to-end on real data: rule + configuration parsing, the combine
# pipeline (free homomorphism), the reducible-configuration blocking path
# (blockedByReducibleConfiguration / representativeDegree / containConf /
# homomorphism), and byte-exact output formatting. The cartwheel enumeration
# engine and check drivers (A.3-A.6) are covered instead by the ported unit-test
# oracles (`lake exe test`), which are exact-equality oracles vs the C++ test
# suite; the full A.3-A.6 enumeration is heavy and intentionally not run here.
#
# Usage: ./p7_differential.sh [NRULES]   (default: all rules)
set -euo pipefail
cd "$(dirname "$0")"

NRULES="${1:-0}" # 0 = all
CPP="${CPP:-../../computer-checks/build/src/main}"   # sibling C++ repo
RUST="${RUST:-../rust_port/target/release/main}"
LEAN="${LEAN:-.lake/build/bin/main}"
# The data repos live in the Rust port dir (already cloned).
DATA="${DATA:-../rust_port}"

[ -x "$CPP" ]  || { echo "C++ oracle not found at $CPP";  exit 1; }
[ -x "$LEAN" ] || { echo "Lean binary not found at $LEAN — run: lake build"; exit 1; }
[ -d "$DATA/discharging-rules/R" ] || { echo "data repos not found under $DATA"; exit 1; }

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
mkdir -p "$WORK/R" "$WORK/empty"
if [ "$NRULES" -eq 0 ]; then
    cp "$DATA"/discharging-rules/R/* "$WORK/R/"
else
    for f in $(ls "$DATA/discharging-rules/R" | sort | head -"$NRULES"); do
        cp "$DATA/discharging-rules/R/$f" "$WORK/R/"
    done
fi
echo "== P7 differential ($(ls "$WORK/R" | wc -l | tr -d ' ') rules, $(ls "$DATA"/reducible-configurations/D/*.conf | wc -l | tr -d ' ') configs) =="

run_one() { # binary outdir <args...>
    local bin="$1" out="$2"; shift 2
    mkdir -p "$out"
    "$bin" "$@" -o "$out" >/dev/null 2>&1
}

diff_against() { # label cpp_out lean_out rust_out
    local label="$1" cpp="$2" lean="$3" rust="$4"
    local ok=1
    if diff -r "$cpp" "$lean" >/dev/null; then echo "  $label Lean vs C++:  IDENTICAL"; else echo "  $label Lean vs C++:  DIFFER"; diff -r "$cpp" "$lean" | head; ok=0; fi
    if [ -x "$RUST" ]; then
        if diff -r "$rust" "$lean" >/dev/null; then echo "  $label Lean vs Rust: IDENTICAL"; else echo "  $label Lean vs Rust: DIFFER"; ok=0; fi
    fi
    [ "$ok" -eq 1 ] || exit 1
}

for lemma in a1 a2; do
    if [ "$lemma" = a1 ]; then C="$WORK/empty"; desc="A.1 (empty C)"; else C="$DATA/reducible-configurations/D"; desc="A.2 (real configs)"; fi
    run_one "$CPP"  "$WORK/cpp_$lemma"  --combine_rules -R "$WORK/R" -C "$C"
    run_one "$LEAN" "$WORK/lean_$lemma" --combine_rules -R "$WORK/R" -C "$C"
    [ -x "$RUST" ] && run_one "$RUST" "$WORK/rust_$lemma" --combine_rules -R "$WORK/R" -C "$C"
    echo "$desc: $(ls "$WORK/cpp_$lemma" | wc -l | tr -d ' ') combined rules"
    diff_against "$desc" "$WORK/cpp_$lemma" "$WORK/lean_$lemma" "$WORK/rust_$lemma"
done
echo "All differential checks passed."
