#!/bin/bash
# Submit the whole insight campaign, one node per job (the jobs are mutually
# independent -- they regenerate their inputs into node-local /dev/shm).
# Run from ~/modi_mount/4ct-checks-rust-lean AFTER modi/insight_preflight.sh.
#
# The check-sweep jobs' 128-thread points double as the control against run
# 229 (expect ~1455 s for the degree-7 check total, ~2921 s for degree 8).
set -euo pipefail
J="modi/insight_job.sh"
sub() { local name="$1" time="$2" mode="$3"; shift 3
  sbatch --job-name "$name" --time "$time" --export=ALL,"$(IFS=,; echo "$*")" "$J" "$mode"; }

sub wheels-sweep   02:00:00 sweep-wheels DEGREE=9
sub check-sweep-l7 06:00:00 sweep-check  DEGREE=7 PORTS=lean
sub check-sweep-r7 02:00:00 sweep-check  DEGREE=7 PORTS=rust
sub check-shard-d7 02:00:00 shard-check  DEGREE=7 PHASE=check_deg7
sub check-shard-d8 02:00:00 shard-check  DEGREE=8 PHASE=check_deg8
sub check-perf-d7  02:00:00 perf-check   DEGREE=7 PHASE=check_deg7
# degree-8 anomaly: the single-thread point plus the 128 control point
sub check-sweep-l8 04:00:00 sweep-check  DEGREE=8 PORTS=lean THREADS="128 1"

squeue -u "$USER"
