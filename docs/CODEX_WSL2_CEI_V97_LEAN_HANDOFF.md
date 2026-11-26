# WSL2 verification of manuscript v97

Set `cei_requested` to the full commit SHA supplied with the final v97 manuscript. Run the following commands from the repository root in WSL2 after the text is fixed.

```bash
set -euo pipefail
git fetch origin main
cei_sha=$(git rev-parse "${cei_requested:?set the full v97 source SHA}^{commit}")
test "$cei_requested" = "$cei_sha"
git merge-base --is-ancestor "$cei_sha" origin/main
cei_work=$(mktemp -d /home/flengyel/src/cei-v97-replay-XXXXXXXX)
git worktree add --detach "$cei_work" "$cei_sha"
cd "$cei_work"
test "$(git rev-parse HEAD)" = "$cei_sha"
test -z "$(git status --porcelain)"
python3 -c 'import json; assert json.load(open("MANUSCRIPT_CURRENT.json"))["version"] == 97'
export PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=1
(cd Lean && lake exe cache get)
python3 scripts/test_verify_axiom_parser.py
python3 scripts/verify.py --manuscript-only
bash scripts/verify-wsl.sh
```

Record the wrapper’s `start-commit`, `exit-status`, and complete verification report. Both independent whole-paper readings must cover the sources at that same commit. For the revised §1, check the two signed bounds, the unique extension of a sentence assignment, and the separator pulled back from the theorem and refutation subobjects of a consistent extension. Check the consistency hypothesis on the signed arithmetic theory and the undecided atom in the endpoint result. Section 4 defines a translation of theories as a logical translation satisfying the theory bound. The scope of Smullyan’s Theorems 22 and 23(b) and the Shoenfield and MPV comparisons are literature attributions. [Correspondence](../FORMALIZATION_STATUS_V97.md) · [Assignment criterion](../Lean/CategoricalEssentialIncompleteness/V46SignedFirstOrderGeneration.lean#L85-L106) · [Pullback of a separator](../Lean/CategoricalEssentialIncompleteness/RestrictionIdempotents.lean#L222)

The [v96 declaration comparison](reviews/V96_LEAN_REASSESSMENT.md) identifies the existing Lean declarations for the conclusions in §1. In v97 the additions on Smullyan, Shoenfield and MPV concern their published results. Check the two links to the registered solution against `cei-v72-palomar-v3` and the remaining Appendix E proof links against `cei-v94-palomar-v4`. The replay and readings cover the manuscript selected by `MANUSCRIPT_CURRENT.json`.

The previous full replay tested manuscript v94 at `b5db36ed4dd2f2b5bfe48f746ff167a95a8a7182`. [v94 report and receipt](V94_WSL2_LEAN_VERIFICATION.md)
