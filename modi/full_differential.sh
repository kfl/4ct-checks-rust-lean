#!/bin/bash
# Full-pipeline 3-way differential (Lemmas A.3-A.6): the heavy follow-up to the
# combine_rules-only p7. Runs, for C++, Rust AND Lean:
#
#   combine_rules -> enum_wheels(-d) -> enum_cartwheels(per wheel) -> check_{deg7,deg8,7triangle}
#
# Every file-producing stage is byte-diffed across the three ports. The check_*
# phases produce no files (success == no assertion fires), so they are compared by
# exit-code AGREEMENT: the ports must agree (all pass, or all fail the same way) —
# a divergence is a port bug. Agreement is meaningful even on a partial slice.
#
# Scope arg picks the cost:
#   modi/full_differential.sh            # degree 7 only — minutes; the cheap GATE
#   modi/full_differential.sh 8          # a different single degree
#   modi/full_differential.sh all        # degrees 7..11 — hours; run under modi_long
#
# Env knobs:
#   WHEEL_LIMIT=N   cap enum_cartwheels to the first N wheels per degree (quick gate)
#   MAX_JOBS=N      parallelism for enum_cartwheels (default: nproc)
#   CPP/RUST/LEAN/DATA  override binary/data locations
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CPP="${CPP:-$(dirname "$ROOT")/computer-checks/build/src/main}"   # sibling C++ repo
RUST="${RUST:-$ROOT/rust_port/target/release/main}"
LEAN="${LEAN:-$ROOT/lean4_port/.lake/build/bin/main}"
DATA="${DATA:-$ROOT/rust_port}"                 # holds the two data repos
R="$DATA/discharging-rules/R"
C="$DATA/reducible-configurations/D"

# Lean needs libleanshared on the library path (recorded by the build, else searched).
LIBDIR="$(cat "$ROOT/.lean_libdir" 2>/dev/null || dirname "$(find "${HOME:-/root}/.elan" /root/.elan -name 'libleanshared*' 2>/dev/null | head -1)" 2>/dev/null || true)"
[ -n "$LIBDIR" ] && export LD_LIBRARY_PATH="$LIBDIR:${LD_LIBRARY_PATH:-}"

case "${1:-7}" in
  all) DEGREES="7 8 9 10 11" ;;
  *)   DEGREES="${1:-7}" ;;
esac
WLIM="${WHEEL_LIMIT:-0}"
MAXJ="${MAX_JOBS:-$(nproc 2>/dev/null || echo 4)}"

for b in "$CPP" "$RUST" "$LEAN"; do [ -x "$b" ] || { echo "missing binary: $b"; exit 1; }; done
[ -d "$R" ] && [ -d "$C" ] || { echo "data repos not found under $DATA (need discharging-rules/R, reducible-configurations/D)"; exit 1; }

PORTS="cpp rust lean"
bin() { case "$1" in cpp) echo "$CPP";; rust) echo "$RUST";; lean) echo "$LEAN";; esac; }

# Scratch on node-local tmpfs (/dev/shm), NOT the shared NFS mount: every
# enum_cartwheels reopens all ~8200 config files, and 128 of them against NFS
# saturate its metadata server, blocking on I/O with the CPUs idle (load ~0).
# Falls back to the default TMPDIR if /dev/shm is unavailable.
WORK="$(mktemp -d /dev/shm/fulldiff.XXXXXX 2>/dev/null || mktemp -d)"; trap 'rm -rf "$WORK"' EXIT
# Stage the read-heavy data into local scratch once; point all runs at the copy.
echo "staging data into $WORK ..."
cp -r "$R" "$WORK/Rdata"; cp -r "$C" "$WORK/Cdata"; R="$WORK/Rdata"; C="$WORK/Cdata"
echo "== Full differential (degrees: $DEGREES${WLIM:+, wheel-limit $WLIM}) on $(uname -sm), $MAXJ-way =="
echo "   C++ =$CPP"; echo "   Rust=$RUST"; echo "   Lean=$LEAN"

# Byte-diff a stage's output dir for rust & lean against the C++ oracle.
diff_stage() { # label subpath
  local label="$1" sub="$2" ok=1
  for p in rust lean; do
    if diff -r "$WORK/cpp/$sub" "$WORK/$p/$sub" >/dev/null 2>&1; then
      echo "  $label: $p == C++  OK"
    else
      echo "  $label: $p != C++  DIVERGENCE"; diff -r "$WORK/cpp/$sub" "$WORK/$p/$sub" 2>&1 | head || true; ok=0
    fi
  done
  [ "$ok" -eq 1 ] || { echo "STOP: divergence at '$label'"; exit 1; }
}

# Published reference counts (paper, Lemmas A.2/A.3): the absolute ground truth the
# ports must ALSO match -- catches a systematic bug where all three agree but are wrong.
EXP_COMBINED=671                                                     # |R*-D|, Lemma A.2
declare -A EXP_WHEELS=( [7]=5439 [8]=6790 [9]=3285 [10]=626 [11]=8 ) # enumPossibleBadWheels
declare -A EXP_BADCW=( [7]=9366 [8]=728 )                            # bad cartwheels w/ tail ranges
PAPER_OK=1
expect() { # label actual [expected]
  local label="$1" act="$2" exp="${3:-}"
  if   [ -z "$exp" ];        then echo "   $label: $act"
  elif [ "$act" = "$exp" ];  then echo "   $label: $act  (paper: $exp)  MATCH"
  else echo "   $label: $act  (paper: $exp)  *** MISMATCH ***"; PAPER_OK=0; fi
}

# --- per-port wall-clock timing: correctness AND approximate speedup in one run ---
declare -A T
now() { date +%s.%N; }
el()  { awk -v a="$1" -v b="$2" 'BEGIN{printf "%.2f", b-a}'; }          # b - a seconds
add() { T[$1]="$(awk -v a="${T[$1]:-0}" -v e="$2" 'BEGIN{printf "%.2f", a+e}')"; }

# ---- Stage 1: combine_rules -> non-blocked combined rules ----
echo "-- combine_rules --"
for p in $PORTS; do
  mkdir -p "$WORK/$p/nb"
  t0=$(now); "$(bin "$p")" --combine_rules -R "$R" -C "$C" -o "$WORK/$p/nb" >/dev/null 2>&1; add "combine:$p" "$(el "$t0" "$(now)")"
done
expect "combined rules" "$(ls "$WORK/cpp/nb" | wc -l | tr -d ' ')" "$EXP_COMBINED"
diff_stage "combine_rules" "nb"

# ---- Stage 2: enum_wheels per degree (uses each port's own non-blocked set) ----
echo "-- enum_wheels --"
for d in $DEGREES; do
  for p in $PORTS; do
    mkdir -p "$WORK/$p/wheels/d$d"
    t0=$(now); "$(bin "$p")" --enum_wheels -d "$d" -R "$R" -C "$C" -S "$WORK/$p/nb" -o "$WORK/$p/wheels/d$d" >/dev/null 2>&1; add "wheels:$p" "$(el "$t0" "$(now)")"
  done
  expect "d$d wheels" "$(ls "$WORK/cpp/wheels/d$d" 2>/dev/null | wc -l | tr -d ' ')" "${EXP_WHEELS[$d]:-}"
  diff_stage "enum_wheels d$d" "wheels/d$d"
done

# ---- Stage 3: enum_cartwheels for every wheel; bad cartwheels accumulate in zero/ ----
echo "-- enum_cartwheels --"
for p in $PORTS; do
  mkdir -p "$WORK/$p/zero"
  bn="$(bin "$p")"
  list="$WORK/$p.wheels"; : > "$list"
  for d in $DEGREES; do ls "$WORK/$p/wheels/d$d"/*.cartwheel 2>/dev/null | sort >> "$list" || true; done
  [ "$WLIM" -gt 0 ] && { head -n "$WLIM" "$list" > "$list.lim" && mv "$list.lim" "$list"; }
  cnt="$(wc -l < "$list" | tr -d ' ')"
  echo "   [$p] enum_cartwheels: $cnt wheels, ${MAXJ}-way ..."
  t0=$(now)
  # xargs -P gives true MAX_JOBS-way concurrency with negligible per-spawn overhead.
  # RAYON_NUM_THREADS=1 / LEAN_NUM_THREADS=1: the ports parallelize config-load internally,
  # so without the cap 128 per-wheel procs each spawn a full thread pool (~16k threads) and
  # oversubscribe the cores. 1 thread/proc x 128 procs = clean 1:1; this takes Rust's cart
  # from 1.22x to 0.90x C++ (measured). The vars are harmless to C++, which ignores them.
  xargs -P "$MAXJ" -I{} env RAYON_NUM_THREADS=1 LEAN_NUM_THREADS=1 \
    "$bn" --enum_cartwheels -w {} -R "$R" -C "$C" -S "$WORK/$p/nb" -o "$WORK/$p/zero" < "$list" >/dev/null 2>&1 || true
  t1=$(now); add "cart:$p" "$(el "$t0" "$t1")"
  echo "   [$p] enum_cartwheels done: $cnt wheels in $(el "$t0" "$t1")s"
done
# Paper gives bad-cartwheel counts only for center degree 7/8, and only a full
# (un-limited) single-degree run is comparable to them.
badexp=""; [ "$(echo $DEGREES | wc -w)" -eq 1 ] && [ "$WLIM" -eq 0 ] && badexp="${EXP_BADCW[$DEGREES]:-}"
expect "bad cartwheels" "$(ls "$WORK/cpp/zero" 2>/dev/null | wc -l | tr -d ' ')" "$badexp"
diff_stage "enum_cartwheels" "zero"

# ---- Stage 4: check_{deg7,deg8,7triangle} -- assertion-only; require exit-code AGREEMENT ----
echo "-- checks (no output files; ports must agree on pass/fail) --"
for chk in check_deg7 check_deg8 check_7triangle; do
  declare -A rc=()
  for p in $PORTS; do
    rc[$p]=0
    t0=$(now); "$(bin "$p")" --"$chk" -W "$WORK/$p/zero" -C "$C" >/dev/null 2>&1 || rc[$p]=$?; add "check:$p" "$(el "$t0" "$(now)")"
  done
  if [ "${rc[cpp]}" = "${rc[rust]}" ] && [ "${rc[cpp]}" = "${rc[lean]}" ]; then
    echo "  $chk: all agree (exit ${rc[cpp]})  OK"
  else
    echo "  $chk: DISAGREE — cpp=${rc[cpp]} rust=${rc[rust]} lean=${rc[lean]}"; exit 1
  fi
done

# --- per-port timing summary (approximate speedup) ---
ratio() { awk -v c="$1" -v x="$2" 'BEGIN{if(c>0)printf "%.2fx",x/c; else printf "-"}'; }   # x/C++
echo "== Per-port wall-clock seconds (degrees $DEGREES; enum_cartwheels is ${MAXJ}-way parallel) =="
printf '   %-16s %10s %10s %10s %10s %10s\n' stage "C++" "Rust" "Lean" "Rust/C++" "Lean/C++"
tc=0; tr=0; tl=0
for s in combine wheels cart check; do
  c="${T[$s:cpp]:-0}"; r="${T[$s:rust]:-0}"; l="${T[$s:lean]:-0}"
  printf '   %-16s %10s %10s %10s %10s %10s\n' "$s" "$c" "$r" "$l" "$(ratio "$c" "$r")" "$(ratio "$c" "$l")"
  tc="$(awk -v a="$tc" -v b="$c" 'BEGIN{printf "%.2f",a+b}')"
  tr="$(awk -v a="$tr" -v b="$r" 'BEGIN{printf "%.2f",a+b}')"
  tl="$(awk -v a="$tl" -v b="$l" 'BEGIN{printf "%.2f",a+b}')"
done
printf '   %-16s %10s %10s %10s %10s %10s\n' TOTAL "$tc" "$tr" "$tl" "$(ratio "$tc" "$tr")" "$(ratio "$tc" "$tl")"

if [ "$PAPER_OK" -eq 1 ]; then
  echo "All checks passed (degrees: $DEGREES): ports agree AND every count matches the published values."
else
  echo "Ports agree, but a count disagrees with the published values (see *** MISMATCH *** above) — degrees: $DEGREES"; exit 1
fi
