#!/bin/bash
# 3-way combine_rules differential (C++ vs Rust vs Lean) on a MODI compute node.
# The C++ binary must already be at computer-checks/build/src/main (the static
# cpp_main from ERDA); Rust + Lean are the in-place ~/modi_mount builds.
#
#   cd ~/modi_mount && sbatch 4ct-checks-rust-lean/modi/p7_job.sh   # submit from
#   cat ~/modi_mount/p7-*.out                  # ~/modi_mount so the output lands here
#
#SBATCH --partition=modi_short
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=8
#SBATCH --time=00:20:00
#SBATCH --output=p7-%j.out
echo "node: $(hostname)"
cd "$HOME/modi_mount/4ct-checks-rust-lean"
# newest stock image -- a pinned name rotates out whenever MODI updates images
IMG="${IMG:-$(ls -t "$HOME"/modi_images/hpc-notebook-*.sif 2>/dev/null | head -1)}"
[ -n "$IMG" ] || IMG=$(ls -t "$HOME"/modi_images/*.sif 2>/dev/null | head -1)
[ -n "$IMG" ] || { echo "no .sif image in ~/modi_images"; exit 1; }
echo "image: $IMG"
apptainer exec --bind "$HOME/modi_mount" \
  "$IMG" modi/run_p7.sh 0
