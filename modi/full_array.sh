#!/bin/bash
# Run the full-pipeline differential for ALL degrees 7..11 as a SLURM job ARRAY:
# one independent whole-node job per degree. Checkpoint + resume via a persistent
# ledger (full-summary.txt) -- re-submitting skips degrees already recorded PASS, so
# a degree that times out or fails never loses the others, and you just re-run the
# stragglers. Each degree's full per-stage detail lands in its own output file.
#
#   cp ~/erda_mount/full_array.sh ~/modi_mount/
#   cd ~/modi_mount && sbatch full_array.sh
#   cat ~/modi_mount/full-summary.txt     # the ledger: one line per finished degree
#   cat ~/modi_mount/full-d8-*.out        # full per-stage detail for a degree
#
# Notes:
#   - %2 caps it at 2 degrees running at once (polite on a shared cluster); raise to
#     %5 to run all five concurrently, or lower to %1 for strictly one-at-a-time.
#   - Already did degree 7 via full_job.sh? Skip it: sbatch --array=8-11%2 full_array.sh
#   - Redo one degree: delete its line from full-summary.txt and re-submit (or just
#     SCOPE=N sbatch full_job.sh).
#
#SBATCH --partition=modi_long
#SBATCH --array=7-11%2
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=128
#SBATCH --exclusive
#SBATCH --mem=0                  # all node RAM: enum_cartwheels runs up to 128 workers,
#SBATCH --time=48:00:00          # each loading the full config/rule set (--exclusive
#SBATCH --output=full-d%a-%A.out # alone may leave the cgroup capped at the 1G default)
set -u
D="$SLURM_ARRAY_TASK_ID"
LEDGER="$HOME/modi_mount/full-summary.txt"

# Resume: if this degree already passed in a previous submission, don't redo it.
if grep -q "degree $D .* PASS" "$LEDGER" 2>/dev/null; then
  echo "degree $D already PASS in $LEDGER -- skipping"; exit 0
fi

echo "node: $(hostname), degree: $D, start $(date '+%F %T')"
cd "$HOME/modi_mount/4ct-checks-rust-lean"
apptainer exec --bind "$HOME/modi_mount" \
  --env MAX_JOBS="${SLURM_CPUS_ON_NODE:-128}" \
  ~/modi_images/hpc-notebook-25.05.6.sif bash modi/full_differential.sh "$D"
rc=$?

verdict="FAIL"; [ "$rc" -eq 0 ] && verdict="PASS"
printf '%s  degree %s  exit=%s  %s\n' "$(date '+%F %T')" "$D" "$rc" "$verdict" >> "$LEDGER"
echo "=> degree $D: $verdict (exit $rc); recorded in $LEDGER"
exit "$rc"
