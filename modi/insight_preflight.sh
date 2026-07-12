#!/bin/bash
# Read-only preflight for the insight campaign; run on the MODI login node from
# ~/modi_mount/4ct-checks-rust-lean. Reports; fixes nothing.
set -uo pipefail
cd "$(dirname "$0")/.."
ok=1; note() { echo "$@"; }; bad() { echo "!! $*"; ok=0; }

echo "== git state (history was rewritten upstream; pull will NOT work)"
git fetch origin 2>/dev/null
LOCAL="$(git rev-parse HEAD 2>/dev/null)"; REMOTE="$(git rev-parse origin/main 2>/dev/null)"
if [ "$LOCAL" = "$REMOTE" ]; then note "   checkout == origin/main ($(git rev-parse --short HEAD))"
elif git merge-base --is-ancestor "$LOCAL" "$REMOTE" 2>/dev/null; then
  bad "checkout is behind origin/main -- run: git reset --hard origin/main   (then rebuild)"
else
  bad "checkout DIVERGES from origin/main (pre-rewrite history) -- run: git reset --hard origin/main   (then rebuild)"
fi
[ -n "$(git status --porcelain 2>/dev/null)" ] && note "   note: local uncommitted changes present"

echo "== binaries (must be rebuilt after any reset)"
for b in rust_port/target/release/main lean4_port/.lake/build/bin/main; do
  if [ -x "$b" ]; then note "   $b  ($(date -r "$b" '+%Y-%m-%d %H:%M'))"; else bad "missing: $b"; fi
done

echo "== data repos"
for d in rust_port/discharging-rules/R rust_port/reducible-configurations/D; do
  [ -d "$d" ] && note "   $d ($(ls "$d" | wc -l | tr -d ' ') files)" || bad "missing: $d"
done

echo "== images"
ls -t "$HOME"/modi_images/*.sif 2>/dev/null | head -3 || bad "no .sif images in ~/modi_images"

echo "== slurm"
sinfo -o '%P %a %l %D %t' 2>/dev/null || bad "sinfo unavailable"
note "   need: >=6 idle nodes; a partition whose time limit covers 6h (check-sweep)"

[ "$ok" -eq 1 ] && echo "PREFLIGHT OK (also run one interactive minute for perf: srun --pty ... perf --version; cat /proc/sys/kernel/perf_event_paranoid)" \
                || { echo "PREFLIGHT FAILED (see !! lines)"; exit 1; }
