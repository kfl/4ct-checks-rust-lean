#!/bin/bash
# linenBench thread-count sweep via sbatch using MODI's STOCK image (no custom
# .sif build, which MODI disallows unprivileged). Assumes the Lean port was
# already built in ~/modi_mount/4ct-checks-rust-lean (elan in $HOME), so
# lean4_port/.lake/build/bin/linenBench exists.
#
# Submit from ~/modi_mount:   sbatch modi/linen_job.sh
# Read the result:            cat ~/modi_mount/linen-*.out
#
#SBATCH --partition=modi_short
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=128      # MODI nodes are 128-core; --exclusive alone leaves the
#SBATCH --exclusive              # cgroup at the default ~2 CPUs, so request them explicitly
#SBATCH --time=01:30:00
#SBATCH --output=linen-%j.out
echo "node: $(hostname), cores: $(nproc)"
cd "$HOME/modi_mount/4ct-checks-rust-lean"
# The 64->128 step of the sweep crosses into SMT (64 physical cores, 2 threads
# each); linen.sh prints lscpu and Cpus_allowed_list so that reading is explicit.
# newest stock image -- a pinned name rotates out whenever MODI updates images
IMG="${IMG:-$(ls -t "$HOME"/modi_images/hpc-notebook-*.sif 2>/dev/null | head -1)}"
[ -n "$IMG" ] || IMG=$(ls -t "$HOME"/modi_images/*.sif 2>/dev/null | head -1)
[ -n "$IMG" ] || { echo "no .sif image in ~/modi_images"; exit 1; }
echo "image: $IMG"
# Five repetitions (plus one untimed warm-up each) per configuration; the c=1
# rows at high thread counts dominate the wall time, so trim REPS or THREADS
# here if the job runs against the partition limit.
apptainer exec --bind "$HOME/modi_mount" \
  --env REPS=5 --env THREADS="1 2 4 8 16 32 64 96 128" \
  "$IMG" modi/linen.sh
