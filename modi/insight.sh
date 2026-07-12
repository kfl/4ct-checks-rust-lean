#!/usr/bin/env bash
# Insight runs following up run 229: where does Lean's many-core time go?
#
#   insight.sh sweep-wheels   enum_wheels wall-clock vs thread count
#   insight.sh sweep-check    the three check_* phases vs thread count
#   insight.sh shard-check    one check phase as SHARDS single-thread processes
#                             (--shard i/n); per-shard wall-clocks -> imbalance
#   insight.sh perf-check     perf stat/record (+ c2c) on an in-process check run
#
# Run inside the container:  apptainer exec IMG modi/insight.sh <mode>
#
# Env knobs:
#   DEGREE=7        wheel centre degree of the staged data
#   THREADS="128 64 32 16 8 4 2 1"  sweep points, descending (cheap points first)
#   PORTS="lean rust"               ports covered by the sweep modes
#   RUNS=1          repetitions per point (min is reported)
#   PHASE=check_deg7  the phase shard-check / perf-check drives
#   SHARDS=128      shard count for shard-check
#   WORKERS=min(SHARDS, cpus)  concurrent shard processes; SHARDS > WORKERS
#                   gives work-stealing (xargs backfills as shards finish)
#   BADCW=dir       pre-staged bad-cartwheel dir; unset -> generated with Rust
#   OUTDIR=$PWD     where .tsv / perf artefacts land
set -euo pipefail
MODE="${1:?usage: insight.sh sweep-wheels|sweep-check|shard-check|perf-check}"

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
RUST="${RUST:-$ROOT/rust_port/target/release/main}"
LEAN="${LEAN:-$ROOT/lean4_port/.lake/build/bin/main}"
CPP="${CPP:-$(dirname "$ROOT")/computer-checks/build/src/main}"     # optional reference
DATA="${DATA:-$ROOT/rust_port}"
LIBDIR="$(cat "$ROOT/.lean_libdir" 2>/dev/null || dirname "$(find "${HOME:-/root}/.elan" /root/.elan -name 'libleanshared*' 2>/dev/null | head -1)" 2>/dev/null || true)"
[ -n "$LIBDIR" ] && export LD_LIBRARY_PATH="$LIBDIR:${LD_LIBRARY_PATH:-}"

DEGREE="${DEGREE:-7}"
PORTS="${PORTS:-lean rust}"
RUNS="${RUNS:-1}"
PHASE="${PHASE:-check_deg7}"
SHARDS="${SHARDS:-128}"
OUTDIR="${OUTDIR:-$PWD}"
NP="${SLURM_CPUS_ON_NODE:-$(nproc --all 2>/dev/null || nproc)}"
THREADS="${THREADS:-}"
if [ -z "$THREADS" ]; then for t in 128 64 32 16 8 4 2 1; do [ "$t" -le "$NP" ] && THREADS="$THREADS $t"; done; fi

for b in "$RUST" "$LEAN"; do [ -x "$b" ] || { echo "missing binary: $b"; exit 1; }; done
echo "== insight $MODE: degree $DEGREE, node $(hostname 2>/dev/null || echo '?'), $NP cpus"
echo "   commit: $(git -C "$ROOT" rev-parse --short HEAD 2>/dev/null || echo '?')"

WORK="$(mktemp -d /dev/shm/insight.XXXXXX 2>/dev/null || mktemp -d)"; trap 'rm -rf "$WORK"' EXIT
cp -r "$DATA/discharging-rules/R" "$WORK/Rdata"
cp -r "$DATA/reducible-configurations/D" "$WORK/Cdata"
R="$WORK/Rdata"; C="$WORK/Cdata"

bin() { case "$1" in rust) echo "$RUST";; lean) echo "$LEAN";; cpp) echo "$CPP";; esac; }
tenv() { case "$1" in rust) echo "RAYON_NUM_THREADS";; lean) echo "LEAN_NUM_THREADS";; cpp) echo "IGNORED_NUM_THREADS";; esac; }
now() { date +%s.%N; }
el() { awk -v a="$1" -v b="$2" 'BEGIN{printf "%.2f", b-a}'; }

# Combined rules (fast, needed by everything downstream); Rust generates --
# all ports' stage outputs are byte-identical, so any port's data serves all.
echo "-- staging: combine_rules (rust)"
mkdir -p "$WORK/nb"
"$RUST" --combine_rules -R "$R" -C "$C" -o "$WORK/nb" >/dev/null 2>&1

stage_badcw() {  # bad cartwheels for $DEGREE into $WORK/zero
  mkdir -p "$WORK/zero"
  if [ -n "${BADCW:-}" ]; then
    echo "-- staging: bad cartwheels from $BADCW"
    cp "$BADCW"/* "$WORK/zero/"
  else
    echo "-- staging: enum_wheels + enum_cartwheels d$DEGREE (rust, ${NP}-way)"
    mkdir -p "$WORK/wheels"
    "$RUST" --enum_wheels -d "$DEGREE" -R "$R" -C "$C" -S "$WORK/nb" -o "$WORK/wheels" >/dev/null 2>&1
    ls "$WORK/wheels"/*.cartwheel | sort | xargs -P "$NP" -I{} env RAYON_NUM_THREADS=1 \
      "$RUST" --enum_cartwheels -w {} -R "$R" -C "$C" -S "$WORK/nb" -o "$WORK/zero" >/dev/null 2>&1 || true
  fi
  echo "   bad cartwheels: $(ls "$WORK/zero" | wc -l | tr -d ' ')"
}

best_of() {  # best_of <runs> <cmd...> -> min wall seconds
  local min="" t0 t1 e
  for _ in $(seq 1 "$1"); do
    t0=$(now); "${@:2}" >/dev/null 2>&1 || true; t1=$(now)
    e="$(el "$t0" "$t1")"
    min="$(awk -v e="$e" -v m="$min" 'BEGIN{print (m==""||e+0<m+0)?e:m}')"
  done
  echo "$min"
}

case "$MODE" in
sweep-wheels)
  TSV="$OUTDIR/insight-wheels-d$DEGREE.tsv"
  echo -e "port\tthreads\tseconds" > "$TSV"
  [ -x "$CPP" ] && { mkdir -p "$WORK/w-cpp"; s="$(best_of "$RUNS" "$CPP" --enum_wheels -d "$DEGREE" -R "$R" -C "$C" -S "$WORK/nb" -o "$WORK/w-cpp")"; echo "   cpp (serial): ${s}s"; echo -e "cpp\t1\t$s" >> "$TSV"; }
  for p in $PORTS; do
    for t in $THREADS; do
      rm -rf "$WORK/w-$p"; mkdir -p "$WORK/w-$p"
      s="$(best_of "$RUNS" env "$(tenv "$p")=$t" "$(bin "$p")" --enum_wheels -d "$DEGREE" -R "$R" -C "$C" -S "$WORK/nb" -o "$WORK/w-$p")"
      echo "   $p x$t: ${s}s"; echo -e "$p\t$t\t$s" >> "$TSV"
    done
  done
  echo "wrote $TSV" ;;

sweep-check)
  stage_badcw
  TSV="$OUTDIR/insight-check-d$DEGREE.tsv"
  echo -e "port\tthreads\tphase\tseconds" > "$TSV"
  for p in $PORTS; do
    for t in $THREADS; do
      total=0
      for chk in check_deg8 check_7triangle check_deg7; do
        s="$(best_of "$RUNS" env "$(tenv "$p")=$t" "$(bin "$p")" --"$chk" -W "$WORK/zero" -C "$C")"
        echo -e "$p\t$t\t$chk\t$s" >> "$TSV"
        total="$(awk -v a="$total" -v b="$s" 'BEGIN{printf "%.2f",a+b}')"
      done
      echo "   $p x$t: ${total}s (per-phase in tsv)"; echo -e "$p\t$t\tALL\t$total" >> "$TSV"
    done
  done
  echo "wrote $TSV" ;;

shard-check)
  stage_badcw
  TSV="$OUTDIR/insight-shard-$PHASE-d$DEGREE.tsv"
  echo -e "shard\tseconds\texit" > "$TSV"
  WORKERS="${WORKERS:-$(( SHARDS < NP ? SHARDS : NP ))}"
  echo "-- $PHASE as $SHARDS x LEAN_NUM_THREADS=1 shards, $WORKERS concurrent"
  t0=$(now)
  cat > "$WORK/shardworker.sh" <<EOF
#!/bin/sh
i="\$1"
t0=\$(date +%s.%N)
env LEAN_NUM_THREADS=1 "$LEAN" --$PHASE -W "$WORK/zero" -C "$C" --shard "\$i/$SHARDS" >/dev/null 2>&1
rc=\$?
t1=\$(date +%s.%N)
printf '%s\t%s\t%s\n' "\$i" "\$(awk -v a="\$t0" -v b="\$t1" 'BEGIN{printf "%.2f", b-a}')" "\$rc" >> "$TSV"
exit \$rc
EOF
  chmod +x "$WORK/shardworker.sh"
  seq 0 $((SHARDS-1)) | xargs -P "$WORKERS" -n 1 "$WORK/shardworker.sh" \
    || echo "   (a shard exited non-zero -- inspect $TSV)"
  wall="$(el "$t0" "$(now)")"
  awk -F'\t' -v wall="$wall" -v n="$WORKERS" 'NR>1{s+=$2; if($2>mx)mx=$2; c++}
    END{if(c>0) printf "   wall %.2fs | %d shards, sum %.2fs, max %.2fs | efficiency (sum/(n*wall)) %.2f\n", wall, c, s, mx, s/(n*wall); else print "   no shards recorded"}' "$TSV"
  echo "wrote $TSV (per-shard wall-clocks; sort -k2 -n for the histogram)" ;;

perf-check)
  stage_badcw
  command -v perf >/dev/null || { echo "perf not available in this image"; exit 1; }
  echo "-- perf_event_paranoid: $(cat /proc/sys/kernel/perf_event_paranoid 2>/dev/null || echo '?')"
  CMDL=(env LEAN_NUM_THREADS="$NP" "$LEAN" --"$PHASE" -W "$WORK/zero" -C "$C")
  echo "-- perf stat"
  perf stat -d -- "${CMDL[@]}" >/dev/null 2>"$OUTDIR/insight-perfstat-$PHASE-d$DEGREE.txt" || true
  tail -25 "$OUTDIR/insight-perfstat-$PHASE-d$DEGREE.txt"
  echo "-- perf record (cycles, 99 Hz)"
  perf record -F 99 -g -o "$WORK/perf.data" -- "${CMDL[@]}" >/dev/null 2>&1 || true
  perf report --stdio --no-children -i "$WORK/perf.data" 2>/dev/null | head -50 \
    | tee "$OUTDIR/insight-perfreport-$PHASE-d$DEGREE.txt"
  cp "$WORK/perf.data" "$OUTDIR/insight-$PHASE-d$DEGREE.perf.data" 2>/dev/null || true
  echo "-- perf c2c (cache-line contention; may be unsupported)"
  if perf c2c record -o "$WORK/c2c.data" -- "${CMDL[@]}" >/dev/null 2>&1; then
    perf c2c report --stdio -i "$WORK/c2c.data" 2>/dev/null | head -40 \
      | tee "$OUTDIR/insight-c2c-$PHASE-d$DEGREE.txt"
  else
    echo "   c2c unavailable on this node/kernel"
  fi ;;

*) echo "unknown mode: $MODE"; exit 1 ;;
esac
