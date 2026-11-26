# WSL2 verification of manuscript v95

Pin the public v95 source commit before starting the replay. From the repository root in WSL2, set `cei_requested` to its full SHA and run these commands.

```bash
set -euo pipefail
git fetch origin main
cei_sha=$(git rev-parse "${cei_requested:?set the full v95 source SHA}^{commit}")
git merge-base --is-ancestor "$cei_sha" origin/main
cei_work=$(mktemp -d /home/flengyel/src/cei-v95-replay-XXXXXXXX)
git worktree add --detach "$cei_work" "$cei_sha"
cd "$cei_work"
test "$(git rev-parse HEAD)" = "$cei_sha"
test -z "$(git status --porcelain)"
python3 -c 'import json; assert json.load(open("MANUSCRIPT_CURRENT.json"))["version"] == 95'
export PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=1
(cd Lean && lake exe cache get)
python3 scripts/test_verify_axiom_parser.py
python3 scripts/verify.py --manuscript-only
bash scripts/verify-wsl.sh
```

Record the wrapper’s `start-commit`, `exit-status`, and complete verification report. Both independent whole-paper readings must cover the sources at that same commit. For the change to §4, check `NullaryInterpretation.atomFormula`, `atom_occurrences`, `atomSentence`, and `atomSentence_inclusion`, together with the generation and extraction adjunction. [Correspondence](../FORMALIZATION_STATUS_V95.md) · [Atom constructor](../Lean/CategoricalEssentialIncompleteness/V46NullarySyntaxInterpretation.lean) · [Adjunction](../Lean/CategoricalEssentialIncompleteness/V46SignedFirstOrderAdjunction.lean)

The previous full replay tested manuscript v94 at `b5db36ed4dd2f2b5bfe48f746ff167a95a8a7182`. [v94 report and receipt](V94_WSL2_LEAN_VERIFICATION.md)
