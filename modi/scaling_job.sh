#!/bin/bash
# Parallel scaling sweep via sbatch using MODI's STOCK image (no custom .sif build,
# which MODI disallows unprivileged). Assumes the Rust + Lean binaries were already
# built in ~/modi_mount/4ct-checks-rust-lean (rustup/elan in $HOME).
#
# Submit from ~/modi_mount:   sbatch modi/scaling_job.sh   (or: sbatch scaling_job.sh)
# Read the result:            cat ~/modi_mount/scaling-*.out
#
#SBATCH --partition=modi_short
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=128      # MODI nodes are 128-core; --exclusive alone leaves the
#SBATCH --exclusive              # cgroup at the default ~2 CPUs, so request them explicitly
#SBATCH --time=00:30:00
#SBATCH --output=scaling-%j.out
echo "node: $(hostname), cores: $(nproc)"
cd "$HOME/modi_mount/4ct-checks-rust-lean"
# scaling.sh locates libleanshared itself (searches $HOME/.elan). RUNS via --env.
# `nproc` mis-reports 2 inside this env even though the job owns all 128 cores
# (Cpus_allowed_list 0-127), so set the sweep explicitly rather than letting
# scaling.sh derive it from nproc.
# newest stock image -- a pinned name rotates out whenever MODI updates images
IMG="${IMG:-$(ls -t "$HOME"/modi_images/hpc-notebook-*.sif 2>/dev/null | head -1)}"
[ -n "$IMG" ] || IMG=$(ls -t "$HOME"/modi_images/*.sif 2>/dev/null | head -1)
[ -n "$IMG" ] || { echo "no .sif image in ~/modi_images"; exit 1; }
echo "image: $IMG"
apptainer exec --bind "$HOME/modi_mount" \
  --env RUNS=3 --env THREADS="1 2 4 8 16 32 64 128" \
  "$IMG" modi/scaling.sh
