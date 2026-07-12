#!/bin/sh
# One-shot setup of the MODI experiments. Run on the MODI Jupyter terminal
# (it has internet; apptainer is not needed for building):
#
#   sftp <you>@io.erda.dk <<< 'put modi/modi_setup.sh'     # from your machine
#   sh ~/erda_mount/modi_setup.sh                          # on the MODI terminal
#
# Idempotent -- safe to rerun. Clones/updates the repo and data repos, stages
# the C++ oracle from the ERDA root, installs rustup/elan into $HOME if
# missing, and builds both ports optimised (cargo --release; lake's default
# buildType is release). Everything the compute nodes must see lands under
# ~/modi_mount; the toolchains live in $HOME (only the login shell builds).

set -eu

REPO_URL=https://github.com/kfl/4ct-checks-rust-lean.git
ROOT="$HOME/modi_mount"
REPO="$ROOT/4ct-checks-rust-lean"
CPP_SRC="$HOME/erda_mount/cpp_main"
CPP_DEST="$ROOT/computer-checks/build/src/main"

[ -d "$ROOT" ] || { echo "error: no $ROOT -- this script must run on MODI"; exit 1; }

echo "== 1/5 this repo"
if [ -d "$REPO/.git" ]; then
  git -C "$REPO" pull --ff-only
else
  git clone "$REPO_URL" "$REPO"
fi

echo "== 2/5 data repos (the differentials read them from rust_port/)"
cd "$REPO/rust_port"
[ -d discharging-rules ] || \
  git clone --depth 1 https://github.com/near-linear-4ct/discharging-rules.git
[ -d reducible-configurations ] || \
  git clone --depth 1 https://github.com/near-linear-4ct/reducible-configurations.git

echo "== 3/5 C++ oracle (static ELF built via modi/Dockerfile, shipped to ERDA root)"
[ -f "$CPP_SRC" ] || { echo "error: $CPP_SRC missing -- the C++ reference cannot be" \
  "compiled on MODI (dependency problems); build it with modi/Dockerfile on a" \
  "Docker-capable machine and sftp the static binary to your ERDA root as cpp_main"; exit 1; }
mkdir -p "$(dirname "$CPP_DEST")"
cp "$CPP_SRC" "$CPP_DEST"
chmod +x "$CPP_DEST"

echo "== 4/5 toolchains (installed to \$HOME if missing)"
if ! command -v cargo >/dev/null 2>&1 && [ ! -x "$HOME/.cargo/bin/cargo" ]; then
  curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal
fi
[ -f "$HOME/.cargo/env" ] && . "$HOME/.cargo/env"
if ! command -v elan >/dev/null 2>&1 && [ ! -x "$HOME/.elan/bin/elan" ]; then
  curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y
fi
PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"
export PATH

echo "== 5/5 build both ports (optimised)"
( cd "$REPO/rust_port" && cargo build --release )
( cd "$REPO/lean4_port" && lake build )   # elan fetches the pinned toolchain (lean-toolchain)

echo
echo "== binaries in place:"
ls -l "$CPP_DEST" "$REPO/rust_port/target/release/main" "$REPO/lean4_port/.lake/build/bin/main"
echo
echo "Next (submit from ~/modi_mount; run the cheap gate FIRST):"
echo "  cd ~/modi_mount && sbatch 4ct-checks-rust-lean/modi/p7_job.sh      # minutes, byte-identical gate"
echo "  cd ~/modi_mount && sbatch 4ct-checks-rust-lean/modi/full_job.sh   # degree-7 full-pipeline gate"
echo "  cd ~/modi_mount && sbatch 4ct-checks-rust-lean/modi/full_array.sh # degrees 7-11, checkpointed"
