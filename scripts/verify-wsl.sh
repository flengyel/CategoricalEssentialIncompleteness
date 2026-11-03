#!/usr/bin/env bash
set -euo pipefail
root=$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$root"
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=1
mkdir -p "$root/.codex-work"
exec 9>"$root/.codex-work/build.lock"
flock -n 9 || { echo 'Another project build or verification is running.' >&2; exit 1; }
run=$(mktemp -d "$root/.codex-work/verify-$(date -u +%Y%m%dT%H%M%SZ)-XXXXXX")
finish() {
  result=$?
  trap - EXIT
  printf '%s\n' "$result" > "$run/exit-status"
  if [[ -d "$root/build-logs" ]]; then cp -a "$root/build-logs" "$run/"; fi
  printf 'Verification exit status: %s; evidence: %s\n' "$result" "$run"
  exit "$result"
}
trap finish EXIT
exec > >(tee "$run/verify.log") 2>&1
date -u '+%Y-%m-%dT%H:%M:%SZ'
git rev-parse HEAD | tee "$run/start-commit"
git status --short --branch | tee "$run/start-status"
git diff --binary > "$run/start-diff.patch"
cp Lean/lean-toolchain Lean/lake-manifest.json "$run/"
(cd Lean && lean --version && lake --version && elan which lean)
printf '%s\n' 'LEAN_NUM_THREADS=1 python3 scripts/verify.py' | tee "$run/command"
python3 scripts/verify.py
