#!/usr/bin/env bash
set -euo pipefail
root=$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$root"
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=1
for command_name in git python3 elan lean lake flock; do
  command -v "$command_name" >/dev/null || {
    printf 'Missing required Linux command: %s\n' "$command_name" >&2; exit 1;
  }
done
[[ $(cat Lean/lean-toolchain) == leanprover/lean4:v4.35.0-rc2 ]] || {
  echo 'Unexpected project toolchain pin; review before installation.' >&2; exit 1;
}
elan toolchain install leanprover/lean4:v4.35.0-rc2
mkdir -p .codex-work
(
  flock -n 9 || { echo 'Another project build is running.' >&2; exit 1; }
  cd Lean
  lean --version
  lake exe cache get
) 9>"$root/.codex-work/build.lock"
exec bash "$root/scripts/verify-wsl.sh"
