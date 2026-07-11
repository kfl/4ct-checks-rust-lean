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
# If the image name differs, edit the .sif below to match `ls ~/modi_images/`.
# `nproc` mis-reports 2 inside this env even though the job owns all 128 cores
# (Cpus_allowed_list 0-127), so set the sweep explicitly rather than letting
# scaling.sh derive it from nproc.
apptainer exec --bind "$HOME/modi_mount" \
  --env RUNS=3 --env THREADS="1 2 4 8 16 32 64 128" \
  ~/modi_images/hpc-notebook-25.05.6.sif modi/scaling.sh
