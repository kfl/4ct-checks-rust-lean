#!/bin/bash
# Focused validation of the tabulation paths (inline factory boundary,
# specialised engine instantiations) across worker counts, via sbatch on
# MODI's stock image. Assumes the Lean port is already built in
# ~/modi_mount/4ct-checks-rust-lean.
#
# Submit from ~/modi_mount:   sbatch modi/tabulate_job.sh
# Read the result:            cat ~/modi_mount/tabulate-*.out
#
# Decisive checks against the M1 baselines:
#   - tabulate stays close to map at matched chunk sizes;
#   - mapIO does not recover a worker-count-dependent success-path floor;
#   - nested tabulation stays budget-bounded;
#   - uneven tabulation keeps normal dynamic-balancing scaling.
#
#SBATCH --partition=modi_short
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=128
#SBATCH --exclusive
#SBATCH --time=01:30:00
#SBATCH --output=tabulate-%j.out
echo "node: $(hostname), cores: $(nproc)"
cd "$HOME/modi_mount/4ct-checks-rust-lean"
IMG="${IMG:-$(ls -t "$HOME"/modi_images/hpc-notebook-*.sif 2>/dev/null | head -1)}"
[ -n "$IMG" ] || IMG=$(ls -t "$HOME"/modi_images/*.sif 2>/dev/null | head -1)
[ -n "$IMG" ] || { echo "no .sif image in ~/modi_images"; exit 1; }
echo "image: $IMG"
apptainer exec --bind "$HOME/modi_mount" \
  --env REPS="${REPS:-5}" --env THREADS="${THREADS:-1 8 32 64 96 128}" \
  --env FILTER="${FILTER:-tabulate,scheduler-map,scheduler-io}" \
  "$IMG" modi/linen.sh
