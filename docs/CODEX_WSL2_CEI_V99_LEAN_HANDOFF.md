# WSL2 verification of manuscript v99

Set `cei_requested` to the full commit SHA supplied with the final v99 manuscript. Run the following commands from the repository root in WSL2 after the text is fixed.

```bash
set -euo pipefail
git fetch origin main
cei_edition_sha=$(git ls-remote --exit-code origin refs/heads/cei-v99-manuscript | cut -f1)
cei_sha=$(git rev-parse "${cei_requested:?set the full v99 source SHA}^{commit}")
test "$cei_requested" = "$cei_sha"
test "$cei_edition_sha" = "$cei_sha"
git merge-base --is-ancestor "$cei_sha" origin/main
cei_work=$(mktemp -d /home/flengyel/src/cei-v99-replay-XXXXXXXX)
git worktree add --detach "$cei_work" "$cei_sha"
cd "$cei_work"
test "$(git rev-parse HEAD)" = "$cei_sha"
test -z "$(git status --porcelain)"
python3 -c 'import json; assert json.load(open("MANUSCRIPT_CURRENT.json"))["version"] == 99'
export PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=1
(cd Lean && lake exe cache get)
python3 scripts/test_verify_axiom_parser.py
python3 scripts/verify.py --manuscript-only
bash scripts/verify-wsl.sh
```

Record the wrapper’s `start-commit`, `exit-status`, and complete verification report. Use that same v99 commit for both independent whole-paper readings under `AGENTS.md`. Record an existing v98 or v97 replay against its assigned commit.

For the universal-property clause of Theorem 4.7, check the object of the comma category, the translation extending each admissible assignment on the whole generator object, and uniqueness with the specified sentence component. Compare that clause with the assignment criterion and adjunction in the correspondence table. Check the Palomar metadata locators against the v99 PDF. Appendix E cites the existing v3 registration. [Manuscript changes](CODEX_MANUSCRIPT_V99_HANDOFF.md) · [Correspondence](../FORMALIZATION_STATUS_V99.md) · [v94 replay and receipt](V94_WSL2_LEAN_VERIFICATION.md)

For a Palomar update from v99, retain both Appendix E citations to the registered v3 record. Use the expected next version only during intake and confirm the assigned version from the public receipt. Select the v99 edition branch and full commit above for the WSL2 replay, both independent whole-paper readings, the official full Comparator preflight, and registration. The preflight must cover that exact commit, including an edition whose changes to Lean sources consist only of comments or metadata. Record its workflow run and passing report before intake; keep the full replay and both completed readings with those records. Obtain the author’s intake and registration approvals as specified in the [Palomar procedure](CODEX_WSL2_PALOMAR_SUBMISSION.md). Confirm the receipt names the identical source SHA. A receipt or preflight for an earlier commit applies to that earlier commit.
