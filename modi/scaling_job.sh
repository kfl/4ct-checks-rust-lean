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
#SBATCH --cpus-per-task=128      # all 128 SMT hardware threads (64 physical cores);
#SBATCH --exclusive              # request them explicitly to avoid the default ~2-CPU cgroup
#SBATCH --time=00:30:00
#SBATCH --output=scaling-%j.out
echo "node: $(hostname), logical CPUs: $(nproc)"
cd "$HOME/modi_mount/4ct-checks-rust-lean"
# scaling.sh locates libleanshared itself (searches $HOME/.elan). RUNS via --env.
# `nproc` mis-reports 2 inside this env even though the job owns all 128 hardware threads
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
