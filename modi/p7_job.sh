#!/bin/bash
# 3-way combine_rules differential (C++ vs Rust vs Lean) on a MODI compute node.
# The C++ binary must already be at computer-checks/build/src/main (the static
# cpp_main from ERDA); Rust + Lean are the in-place ~/modi_mount builds.
#
#   cp ~/erda_mount/p7_job.sh ~/modi_mount/
#   cd ~/modi_mount && sbatch p7_job.sh        # submit from ~/modi_mount so the
#   cat ~/modi_mount/p7-*.out                  # relative output lands here
#
#SBATCH --partition=modi_short
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=8
#SBATCH --time=00:20:00
#SBATCH --output=p7-%j.out
echo "node: $(hostname)"
cd "$HOME/modi_mount/4ct-checks-rust-lean"
apptainer exec --bind "$HOME/modi_mount" \
  ~/modi_images/hpc-notebook-25.05.6.sif modi/run_p7.sh 0
