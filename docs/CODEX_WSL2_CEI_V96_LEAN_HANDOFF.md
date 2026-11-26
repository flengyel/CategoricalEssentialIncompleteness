# WSL2 verification of manuscript v96

The [declaration comparison](reviews/V96_LEAN_REASSESSMENT.md) covers manuscript v96 at `ff20da56315d405f92ccd4f587fe4c05f32e11d2`. Let ongoing reviews finish. Run the full replay after the manuscript incorporates the accepted additions and corrections. If these produce a later edition, use its manifest and verification handoff and reconcile its new assertions first. For a replay of v96, set `cei_requested` to the full v96 source SHA above and run these commands from the repository root in WSL2.

```bash
set -euo pipefail
git fetch origin main
cei_sha=$(git rev-parse "${cei_requested:?set the full v96 source SHA}^{commit}")
git merge-base --is-ancestor "$cei_sha" origin/main
cei_work=$(mktemp -d /home/flengyel/src/cei-v96-replay-XXXXXXXX)
git worktree add --detach "$cei_work" "$cei_sha"
cd "$cei_work"
test "$(git rev-parse HEAD)" = "$cei_sha"
test -z "$(git status --porcelain)"
python3 -c 'import json; assert json.load(open("MANUSCRIPT_CURRENT.json"))["version"] == 96'
export PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=1
(cd Lean && lake exe cache get)
python3 scripts/test_verify_axiom_parser.py
python3 scripts/verify.py --manuscript-only
bash scripts/verify-wsl.sh
```

Record the wrapper’s `start-commit`, `exit-status`, and complete verification report. Both independent whole-paper readings must cover the sources at that same commit. For the revised §1, check the two signed bounds, the unique extension of a sentence assignment, and the separator pulled back from the theorem and refutation subobjects of a consistent extension. Check the consistency hypothesis on the signed arithmetic theory and the undecided atom in the endpoint result. Section 4 defines a translation of theories as a logical translation satisfying the theory bound. The scope of Smullyan’s Theorems 22 and 23(b) and the Shoenfield and MPV comparisons are literature attributions. [Correspondence](../FORMALIZATION_STATUS_V96.md) · [Assignment criterion](../Lean/CategoricalEssentialIncompleteness/V46SignedFirstOrderGeneration.lean#L85-L106) · [Pullback of a separator](../Lean/CategoricalEssentialIncompleteness/RestrictionIdempotents.lean#L222)

The previous full replay tested manuscript v94 at `b5db36ed4dd2f2b5bfe48f746ff167a95a8a7182`. [v94 report and receipt](V94_WSL2_LEAN_VERIFICATION.md)
