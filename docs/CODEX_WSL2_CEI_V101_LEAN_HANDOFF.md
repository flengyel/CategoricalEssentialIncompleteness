# WSL2 verification of manuscript v101

Set `cei_requested` to the full commit SHA supplied with the final v101 manuscript. Run the following commands from the repository root in WSL2 after the text is fixed.

```bash
set -euo pipefail
git fetch origin main
cei_edition_sha=$(git ls-remote --exit-code origin refs/heads/cei-v101-manuscript | cut -f1)
cei_sha=$(git rev-parse "${cei_requested:?set the full v101 source SHA}^{commit}")
test "$cei_requested" = "$cei_sha"
test "$cei_edition_sha" = "$cei_sha"
git merge-base --is-ancestor "$cei_sha" origin/main
cei_work=$(mktemp -d /home/flengyel/src/cei-v101-replay-XXXXXXXX)
git worktree add --detach "$cei_work" "$cei_sha"
cd "$cei_work"
test "$(git rev-parse HEAD)" = "$cei_sha"
test -z "$(git status --porcelain)"
python3 -c 'import json; assert json.load(open("MANUSCRIPT_CURRENT.json"))["version"] == 101'
export PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=1
(cd Lean && lake exe cache get)
python3 scripts/test_verify_axiom_parser.py
python3 scripts/verify.py --manuscript-only
bash scripts/verify-wsl.sh
```

Record the wrapper’s `start-commit`, `exit-status`, and complete verification report. Use that same v101 commit for both independent whole-paper readings under `AGENTS.md`. The last recorded full replay and both readings tested v94 at `b5db36ed4dd2f2b5bfe48f746ff167a95a8a7182`. Record any replay or reading of v100 at its tested commit, `145c2a2bc3e1f307b1bbc12b1418a6ec8e3fdbbb`.

In the preface, reconstruct the numerical proof of Corollary 8.4: Lemma 8.1 supplies the map on sentence codes, and the standard interpretation takes the partial lift used in Corollary 3.2 to the total recursive conditional. Check against Theorem 5.2 that its two adjunctions concern the underlying categories. Confirm the four Palomar page locators against the final PDF and the registered-source citations in Appendix E. Record the full replay, both independent readings and the full Comparator result separately against the same source commit. [Manuscript changes](CODEX_MANUSCRIPT_V101_HANDOFF.md) · [Correspondence](../FORMALIZATION_STATUS_V101.md) · [v94 replay and receipt](V94_WSL2_LEAN_VERIFICATION.md)

For a Palomar update from v101, retain both Appendix E citations to the registered v3 record. Use the expected next version only during intake and confirm the assigned version from the public receipt. Select the v101 edition branch and full commit above for the WSL2 replay, both independent whole-paper readings, the official full Comparator preflight, and registration. The preflight must cover that exact commit, including an edition whose changes to Lean sources consist only of comments or metadata. Record its workflow run and passing report before intake; keep the full replay and both completed readings with those records. Obtain the author’s intake and registration approvals as specified in the [Palomar procedure](CODEX_WSL2_PALOMAR_SUBMISSION.md). Confirm the receipt names the identical source SHA. A receipt or preflight for an earlier commit applies to that earlier commit.
