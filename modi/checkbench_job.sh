#!/bin/bash
# Repeated-run check bench on the real check phases (Lean only) via sbatch
# using MODI's STOCK image. Assumes the Lean port was already built in
# ~/modi_mount/4ct-checks-rust-lean (elan in $HOME).
#
# Submit from ~/modi_mount:   sbatch 4ct-checks-rust-lean/modi/checkbench_job.sh
# Read the result:            cat ~/modi_mount/checkbench-*.out
#
# Defaults: d7 corpus, t=96, one rep, both d7 check phases (see
# modi/checkbench.sh). A thread-scaling sweep with repetitions:
#   THREADS="32 64 96 128" REPS=3 sbatch --export=ALL \
#     4ct-checks-rust-lean/modi/checkbench_job.sh
# Reuse a staged corpus with BENCH_CORPUS=$HOME/modi_mount/<corpus-dir>.
#
#SBATCH --partition=modi_long
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=128      # whole node; --exclusive alone leaves the cgroup
#SBATCH --exclusive              # at ~2 CPUs, so request them explicitly
#SBATCH --mem=0                  # all node RAM (checks + 128-way prep)
#SBATCH --time=06:00:00
#SBATCH --output=checkbench-%j.out
echo "node: $(hostname), cores: $(nproc)"
cd "$HOME/modi_mount/4ct-checks-rust-lean"
# newest stock image -- a pinned name rotates out whenever MODI updates images
IMG="${IMG:-$(ls -t "$HOME"/modi_images/hpc-notebook-*.sif 2>/dev/null | head -1)}"
[ -n "$IMG" ] || IMG=$(ls -t "$HOME"/modi_images/*.sif 2>/dev/null | head -1)
[ -n "$IMG" ] || { echo "no .sif image in ~/modi_images"; exit 1; }
echo "image: $IMG"
apptainer exec --bind "$HOME/modi_mount" \
  --env DEGREES="${DEGREES:-7}" --env CHECKS="${CHECKS:-check_7triangle check_deg7}" \
  --env THREADS="${THREADS:-96}" --env REPS="${REPS:-1}" \
  --env WHEEL_LIMIT="${WHEEL_LIMIT:-0}" --env MAX_JOBS="${SLURM_CPUS_ON_NODE:-128}" \
  --env BENCH_CORPUS="${BENCH_CORPUS:-}" --env BENCH_LOGDIR="${BENCH_LOGDIR:-}" \
  "$IMG" modi/checkbench.sh
