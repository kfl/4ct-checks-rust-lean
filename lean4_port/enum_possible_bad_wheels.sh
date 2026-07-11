#!/bin/bash
# Port of ../enum_possible_bad_wheels.sh, driving the Lean binary instead of the
# C++ one. Build it first with `lake build` (or set BIN to the binary path).
set -exuo pipefail
cd "$(dirname "$0")"

BIN="${BIN:-.lake/build/bin/main}"

for d in $(seq 7 11); do
    "$BIN" --enum_wheels -d "$d" -R discharging-rules/R -C reducible-configurations/D -S combined_rules/non_blocked -o "wheels/d$d" > "log/wheels_d$d.log" &
done
