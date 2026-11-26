# WSL2 verification of manuscript v98

Set `cei_requested` to the full commit SHA supplied with the final v98 manuscript. Run the following commands from the repository root in WSL2 after the text is fixed.

```bash
set -euo pipefail
git fetch origin main
cei_edition_sha=$(git ls-remote --exit-code origin refs/heads/cei-v98-manuscript | cut -f1)
cei_sha=$(git rev-parse "${cei_requested:?set the full v98 source SHA}^{commit}")
test "$cei_requested" = "$cei_sha"
test "$cei_edition_sha" = "$cei_sha"
git merge-base --is-ancestor "$cei_sha" origin/main
cei_work=$(mktemp -d /home/flengyel/src/cei-v98-replay-XXXXXXXX)
git worktree add --detach "$cei_work" "$cei_sha"
cd "$cei_work"
test "$(git rev-parse HEAD)" = "$cei_sha"
test -z "$(git status --porcelain)"
python3 -c 'import json; assert json.load(open("MANUSCRIPT_CURRENT.json"))["version"] == 98'
export PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=1
(cd Lean && lake exe cache get)
python3 scripts/test_verify_axiom_parser.py
python3 scripts/verify.py --manuscript-only
bash scripts/verify-wsl.sh
```

Record the wrapper’s `start-commit`, `exit-status`, and complete verification report. Use that same v98 commit for both independent whole-paper readings under `AGENTS.md`. An existing v97 run may finish at `1dccf0d1037e8268f29cb5d7593c5cda7ac5d417` and be recorded against v97.

The v98 abstract shortens the sentence connecting diagonal pairs to internal theories. Check the manuscript URL and the three statement references in `Lean/formalization.yaml` against the rebuilt v98 PDF. Appendix E cites the existing v3 registration. [Manuscript changes](CODEX_MANUSCRIPT_V98_HANDOFF.md) · [Correspondence](../FORMALIZATION_STATUS_V98.md) · [v94 replay and receipt](V94_WSL2_LEAN_VERIFICATION.md)
