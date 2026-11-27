# WSL2 verification of manuscript v103

Set `cei_requested` to the full SHA supplied for `cei-v103-palomar-candidate`. Run the following commands from the repository root in WSL2. The v102 manuscript was fixed at `e1a145a74f05cfb549e47ca9ee0c867e415ace08`. Its Palomar candidate, including the revised statement-file notes, was `94bf26d378a3ac44650c0439f5b82c3c8f930cfa`.

```bash
set -euo pipefail
git fetch origin refs/heads/main:refs/remotes/origin/main refs/heads/cei-v103-palomar-candidate:refs/remotes/origin/cei-v103-palomar-candidate
cei_candidate_sha=$(git rev-parse 'refs/remotes/origin/cei-v103-palomar-candidate^{commit}')
cei_sha=$(git rev-parse "${cei_requested:?set the full v103 Palomar candidate SHA}^{commit}")
test "$cei_requested" = "$cei_sha"
test "$cei_candidate_sha" = "$cei_sha"
git merge-base --is-ancestor "$cei_sha" origin/main
cei_work=$(mktemp -d /home/flengyel/src/cei-v103-replay-XXXXXXXX)
git worktree add --detach "$cei_work" "$cei_sha"
cd "$cei_work"
test "$(git rev-parse HEAD)" = "$cei_sha"
test -z "$(git status --porcelain)"
python3 -c 'import json; assert json.load(open("MANUSCRIPT_CURRENT.json"))["version"] == 103'
export PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=1
(cd Lean && lake exe cache get)
python3 scripts/test_verify_axiom_parser.py
python3 scripts/verify.py --manuscript-only
bash scripts/verify-wsl.sh
```

Record the wrapper’s `start-commit`, `exit-status`, and complete verification report. Use that same v103 commit for both independent whole-paper readings under `AGENTS.md`. The last recorded full replay and both readings tested v94 at `b5db36ed4dd2f2b5bfe48f746ff167a95a8a7182`. Keep any v102 receipts with their tested commit.

In the preface, reconstruct the numerical proof of Corollary 8.4: Lemma 8.1 supplies the map from natural numbers to sentence codes. In the proof of Corollary 8.4, an index for the conditional deciding membership in the inverse image gives a partial morphism in the syntactic category. Its standard interpretation is the conditional, so Corollary 3.2 rules out the separator. Check against Theorem 5.2 that its two adjunctions concern the underlying categories. For the additional preface paragraph, check the quantifiers over programs, representations and subsets in Corollary 9.4, and the compatibility of computable decisions at the three vertices in the proof about complementary subdiagrams. Confirm the four Palomar page locators against the final PDF and the registered-source citations in Appendix E. Record the full replay, both independent readings and the full Comparator result separately against the same source commit. [Manuscript changes](CODEX_MANUSCRIPT_V103_HANDOFF.md) · [Correspondence](../FORMALIZATION_STATUS_V103.md) · [v94 replay and receipt](V94_WSL2_LEAN_VERIFICATION.md)

Palomar’s **“Notes from the statement file”** displays the first `/-! … -/` comment in [CEIPalomar/Challenge.lean](../Lean/CEIPalomar/Challenge.lean). The entry abstract comes from `project.description` in [formalization.yaml](../Lean/formalization.yaml). Compare the parsed description with [PALOMAR_ABSTRACT.txt](PALOMAR_ABSTRACT.txt), omitting the text file’s final newline. Its second paragraph identifies the three selected statements.

At preflight, check that the mechanical report’s `source.commit` equals `cei_requested` and its `formalization.sha256` equals the SHA-256 of `Lean/formalization.yaml` at that commit. When Palomar produces the render for this candidate, compare the decoded `module_doc` field of its `challenge-metadata.json` with the opening comment in the candidate’s statement file. The renderer removes the delimiters and trims the outer whitespace. The expected SHA-256 of the resulting UTF-8 text is `e12cd7d9831f1e91a6ead9803514ccda083a4ed936c4db3be42090818b86339e`. It covers Theorem 4.7’s universal property for assignments on all of X, Corollary 4.8, the Boolean assignment and the existence consequence of Lemma 8.9. [Extraction](https://github.com/PalomarRegistry/PalomarSubmission/blob/046554302064b2c83c2b924bea6db87fc5900c68/scripts/render_challenge.py#L583-L598)

Run the Palomar checks in §3 of the [release procedure](CODEX_WSL2_PALOMAR_SUBMISSION.md) at the candidate SHA, including the full Comparator preflight. Its configuration permits `propext`, `Quot.sound` and `Classical.choice` for the selected theorems. The two-axiom regression in `Lean/Tests/AxiomRegression.lean` concerns three Rice–Shapiro declarations. Keep the passing preflight, full WSL2 replay and both readings with their tested SHA. For intake and registration follow §4 of the release procedure. Verify that the public receipt names that same SHA and that the new record displays the approved description and the candidate’s statement-file notes. Appendix E cites the published v3 record.
