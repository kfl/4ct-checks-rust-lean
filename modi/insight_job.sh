#!/bin/bash
# sbatch wrapper for one insight.sh mode on one full node (stock image, like
# scaling_job.sh). Mode is $1; knobs (DEGREE, THREADS, PORTS, RUNS, PHASE,
# SHARDS, BADCW) pass through the environment:
#
#   sbatch --time=6:00:00 --export=ALL,DEGREE=7,PORTS=lean modi/insight_job.sh sweep-check
#
#SBATCH --partition=modi_short
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=128      # MODI nodes are 128-core; --exclusive alone leaves the
#SBATCH --exclusive              # cgroup at the default ~2 CPUs, so request them explicitly
#SBATCH --time=02:00:00
#SBATCH --output=insight-%x-%j.out
MODE="${1:?mode required: sweep-wheels|sweep-check|shard-check|perf-check}"
cd "$HOME/modi_mount/4ct-checks-rust-lean"

echo "node: $(hostname), mode: $MODE, degree: ${DEGREE:-7}"
echo "commit: $(git rev-parse --short HEAD 2>/dev/null || echo '?')"

# Guard against the known cgroup trap: the job must really own the node's CPUs.
ALLOWED="$(grep Cpus_allowed_list /proc/self/status | awk '{print $2}')"
echo "cpus allowed: $ALLOWED"
NCPU="$(python3 -c "
spans='$ALLOWED'.split(',')
print(sum(int(s.split('-')[1])-int(s.split('-')[0])+1 if '-' in s else 1 for s in spans))" 2>/dev/null || echo 0)"
if [ "${NCPU:-0}" -lt 100 ] && [ -z "${FORCE:-}" ]; then
  echo "ABORT: cgroup grants only $NCPU CPUs (need ~128; FORCE=1 to override)"; exit 1
fi

# Newest stock image -- log which one, so an image rotation mid-campaign is
# visible in every output file. (A pinned name rotates out on MODI updates.)
IMG="${IMG:-$(ls -t "$HOME"/modi_images/hpc-notebook-*.sif 2>/dev/null | head -1)}"
[ -n "$IMG" ] || IMG=$(ls -t "$HOME"/modi_images/*.sif 2>/dev/null | head -1)
[ -n "$IMG" ] || { echo "no .sif image in ~/modi_images"; exit 1; }
echo "image: $IMG ($(date -r "$IMG" '+%Y-%m-%d' 2>/dev/null || echo '?'))"

ENVARGS=()
for v in DEGREE THREADS PORTS RUNS PHASE SHARDS BADCW OUTDIR; do
  [ -n "${!v:-}" ] && ENVARGS+=(--env "$v=${!v}")
done
apptainer exec --bind "$HOME/modi_mount" "${ENVARGS[@]}" "$IMG" modi/insight.sh "$MODE"
