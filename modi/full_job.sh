#!/bin/bash
# Full-pipeline 3-way differential on a MODI compute node.
#
# Cheap GATE (degree 7, minutes) — validate the machinery first:
#   cp ~/erda_mount/full_job.sh ~/modi_mount/
#   cd ~/modi_mount && sbatch full_job.sh
#   cat ~/modi_mount/full-*.out
#
# Even quicker smoke test (first 20 wheels of degree 7):
#   cd ~/modi_mount && WHEEL_LIMIT=20 sbatch --export=ALL full_job.sh
#
# FULL run (degrees 7..11, hours) once the gate is green — override on the CLI:
#   cd ~/modi_mount && SCOPE=all sbatch --export=ALL --partition=modi_long --time=24:00:00 full_job.sh
#
#SBATCH --partition=modi_short
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=128     # whole 128-core node; enum_cartwheels is embarrassingly
#SBATCH --exclusive             # parallel, so MAX_JOBS below tracks the full allocation
#SBATCH --mem=0                 # all node RAM (else the cgroup may cap at the 1G default,
#SBATCH --time=02:00:00         # OOM-killing the 128 enum_cartwheels workers)
#SBATCH --output=full-%j.out
SCOPE="${SCOPE:-7}"
echo "node: $(hostname), scope: $SCOPE, wheel_limit: ${WHEEL_LIMIT:-none}"
cd "$HOME/modi_mount/4ct-checks-rust-lean"
apptainer exec --bind "$HOME/modi_mount" \
  --env WHEEL_LIMIT="${WHEEL_LIMIT:-0}" --env MAX_JOBS="${SLURM_CPUS_ON_NODE:-128}" \
  ~/modi_images/hpc-notebook-25.05.6.sif bash modi/full_differential.sh "$SCOPE"
