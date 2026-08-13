#!/usr/bin/env bash
# Repeated-run harness for the REAL check phases (Lean only): one build, a
# thread sweep, and REPS repetitions per configuration, recording wall, user,
# and system seconds, max RSS, and Linen's worker-budget statistics
# (--budget_stats) per run.
#
# Correctness gate: every run must exit 0 and produce a check log
# byte-identical to the first run of the same check -- across repetitions AND
# thread counts, since the combinators are order-preserving and results are
# scheduling-independent by construction. The budget-statistics line is
# stripped before comparing.
#
#   modi/checkbench.sh                              # d7 corpus, t=96, one rep
#   THREADS="32 64 96 128" REPS=3 modi/checkbench.sh
#   REPS=0 modi/checkbench.sh                       # prep-only (stage a corpus)
#   WHEEL_LIMIT=5 modi/checkbench.sh                # smoke test
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"

LEAN="$ROOT/lean4_port/.lake/build/bin/main"
[ -x "$LEAN" ] || { echo "lean main not built: $LEAN"; exit 1; }
R="$ROOT/rust_port/discharging-rules/R"
C="$ROOT/rust_port/reducible-configurations/D"

DEGREES="${DEGREES:-7}"
THREADS="${THREADS:-96}"
REPS="${REPS:-1}"
CHECKS="${CHECKS:-check_7triangle check_deg7}"
WLIM="${WHEEL_LIMIT:-0}"
MAXJ="${MAX_JOBS:-$(nproc --all 2>/dev/null || nproc)}"

echo "## check-phase repeated-run bench (Lean only)"
echo "commit: $(git -C "$ROOT" rev-parse HEAD 2>/dev/null || echo unknown)$(git -C "$ROOT" diff --quiet 2>/dev/null || echo ' (dirty)')"
echo "image: ${APPTAINER_CONTAINER:-${SINGULARITY_CONTAINER:-unknown}}"
grep Cpus_allowed_list /proc/self/status || true
echo "degrees: $DEGREES, threads: $THREADS, reps: $REPS, checks: $CHECKS, wheel_limit: $WLIM"

WORK="$(mktemp -d /dev/shm/linencb.XXXXXX 2>/dev/null || mktemp -d)"; trap 'rm -rf "$WORK"' EXIT

# ---- Corpus: reuse a shared staged corpus (BENCH_CORPUS) or stage a private
# ---- one. The marker records degrees/wheel-limit so a stale or mismatched
# ---- shared corpus can never be silently reused.
CORPUS="${BENCH_CORPUS:-$WORK/corpus}"
if [ -f "$CORPUS/.complete" ]; then
  [ "$(cat "$CORPUS/marker" 2>/dev/null)" = "$DEGREES/$WLIM" ] || {
    echo "STOP: corpus at $CORPUS was staged for '$(cat "$CORPUS/marker" 2>/dev/null)', want '$DEGREES/$WLIM'"; exit 1; }
  echo "-- reusing staged corpus at $CORPUS ($(ls "$CORPUS/zero" | wc -l | tr -d ' ') bad cartwheels) --"
else
  echo "-- prep (into $CORPUS) --"
  mkdir -p "$CORPUS/nb" "$CORPUS/zero"
  "$LEAN" --combine_rules -R "$R" -C "$C" -o "$CORPUS/nb" >/dev/null
  for d in $DEGREES; do
    mkdir -p "$CORPUS/wheels/d$d"
    "$LEAN" --enum_wheels -d "$d" -R "$R" -C "$C" -S "$CORPUS/nb" -o "$CORPUS/wheels/d$d" >/dev/null
  done
  list="$CORPUS/wheels.list"; : > "$list"
  for d in $DEGREES; do ls "$CORPUS/wheels/d$d"/*.cartwheel 2>/dev/null | sort >> "$list" || true; done
  [ "$WLIM" -gt 0 ] && { head -n "$WLIM" "$list" > "$list.lim" && mv "$list.lim" "$list"; }
  echo "   wheels: $(wc -l < "$list" | tr -d ' '), enum_cartwheels ${MAXJ}-way ..."
  xargs -P "$MAXJ" -I{} env LEAN_NUM_THREADS=1 \
    "$LEAN" --enum_cartwheels -w {} -R "$R" -C "$C" -S "$CORPUS/nb" -o "$CORPUS/zero" < "$list" >/dev/null 2>&1 || true
  echo "   bad cartwheels: $(ls "$CORPUS/zero" | wc -l | tr -d ' ')"
  echo "$DEGREES/$WLIM" > "$CORPUS/marker"
  touch "$CORPUS/.complete"
fi

# Resource capture via modi/rusage.py (python3): the MODI stock image has no
# GNU time, and python3 is everywhere we run.
RUSAGE=""; command -v python3 >/dev/null 2>&1 && RUSAGE="$ROOT/modi/rusage.py"

for t in $THREADS; do
  for r in $(seq 1 "$REPS"); do
    for chk in $CHECKS; do
      log="$WORK/log"; tf="$WORK/time"
      set +e
      if [ -n "$RUSAGE" ]; then
        env LEAN_NUM_THREADS="$t" \
          python3 "$RUSAGE" "$tf" "$LEAN" --"$chk" --budget_stats -W "$CORPUS/zero" -C "$C" > "$log" 2>&1
        rc=$?
      else
        t0=$(date +%s.%N)
        env LEAN_NUM_THREADS="$t" \
          "$LEAN" --"$chk" --budget_stats -W "$CORPUS/zero" -C "$C" > "$log" 2>&1
        rc=$?; awk -v a="$t0" -v b="$(date +%s.%N)" 'BEGIN{printf "wall=%.2fs (fallback)\n", b-a}' > "$tf"
      fi
      set -e
      line="t=$t rep=$r $chk: rc=$rc $(cat "$tf")"
      echo "$line"
      stats="$(grep '^budget:' "$log" || true)"
      [ -z "$stats" ] || echo "   $stats"
      [ "$rc" -eq 0 ] || { echo "STOP: $chk failed (t=$t rep=$r)"; tail -5 "$log"; exit 1; }
      # Gate: logs must be byte-identical across repetitions and thread
      # counts (budget-statistics line stripped).
      grep -v '^budget:' "$log" > "$log.clean"
      if [ ! -f "$WORK/ref.$chk" ]; then
        cp "$log.clean" "$WORK/ref.$chk"
      elif ! cmp -s "$log.clean" "$WORK/ref.$chk"; then
        echo "STOP: $chk log DIVERGES from baseline (t=$t rep=$r)"
        diff "$WORK/ref.$chk" "$log.clean" | head; exit 1
      fi
      # Persist cleaned logs and timings for cross-job comparison.
      if [ -n "${BENCH_LOGDIR:-}" ]; then
        mkdir -p "$BENCH_LOGDIR"
        echo "$line" >> "$BENCH_LOGDIR/timings.txt"
        [ -z "$stats" ] || echo "   $stats" >> "$BENCH_LOGDIR/timings.txt"
        cp "$log.clean" "$BENCH_LOGDIR/$chk.t$t.r$r.log"
      fi
    done
  done
done
if [ "$REPS" -gt 0 ]; then echo "## all runs agree with the baseline logs"; else echo "## prep-only run complete"; fi
