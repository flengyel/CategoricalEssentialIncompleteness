# WSL2 verification of manuscript v102

Set `cei_requested` to the full commit SHA supplied with the final v102 manuscript. Run the following commands from the repository root in WSL2 after the text is fixed.

```bash
set -euo pipefail
git fetch origin main
cei_edition_sha=$(git ls-remote --exit-code origin refs/heads/cei-v102-manuscript | cut -f1)
cei_sha=$(git rev-parse "${cei_requested:?set the full v102 source SHA}^{commit}")
test "$cei_requested" = "$cei_sha"
test "$cei_edition_sha" = "$cei_sha"
git merge-base --is-ancestor "$cei_sha" origin/main
cei_work=$(mktemp -d /home/flengyel/src/cei-v102-replay-XXXXXXXX)
git worktree add --detach "$cei_work" "$cei_sha"
cd "$cei_work"
test "$(git rev-parse HEAD)" = "$cei_sha"
test -z "$(git status --porcelain)"
python3 -c 'import json; assert json.load(open("MANUSCRIPT_CURRENT.json"))["version"] == 102'
export PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=1
(cd Lean && lake exe cache get)
python3 scripts/test_verify_axiom_parser.py
python3 scripts/verify.py --manuscript-only
bash scripts/verify-wsl.sh
```

Record the wrapper’s `start-commit`, `exit-status`, and complete verification report. Use that same v102 commit for both independent whole-paper readings under `AGENTS.md`. The last recorded full replay and both readings tested v94 at `b5db36ed4dd2f2b5bfe48f746ff167a95a8a7182`. The preceding v101 edition was `d751072f38626106aa8654320499c7a2486404dc`. Record earlier receipts at their tested commits.

In the preface, reconstruct the numerical proof of Corollary 8.4: Lemma 8.1 supplies the map from natural numbers to sentence codes. In the proof of Corollary 8.4, an index for the conditional deciding membership in the inverse image gives a partial morphism in the syntactic category. Its standard interpretation is the conditional, so Corollary 3.2 rules out the separator. Check against Theorem 5.2 that its two adjunctions concern the underlying categories. Confirm the four Palomar page locators against the final PDF and the registered-source citations in Appendix E. Record the full replay, both independent readings and the full Comparator result separately against the same source commit. [Manuscript changes](CODEX_MANUSCRIPT_V102_HANDOFF.md) · [Correspondence](../FORMALIZATION_STATUS_V102.md) · [v94 replay and receipt](V94_WSL2_LEAN_VERIFICATION.md)

For a Palomar update from v102, retain both Appendix E citations to the registered v3 record. Use the expected next version only during intake and confirm the assigned version from the public receipt. Select the v102 edition branch and full commit above for the WSL2 replay, both independent whole-paper readings, the official full Comparator preflight, and registration. The preflight must cover that exact commit, including an edition whose changes to Lean sources consist only of comments or metadata. Record its workflow run and passing report before intake; keep the full replay and both completed readings with those records. Obtain the author’s intake and registration approvals as specified in the [Palomar procedure](CODEX_WSL2_PALOMAR_SUBMISSION.md). Confirm the receipt names the identical source SHA. A receipt or preflight for an earlier commit applies to that earlier commit.
