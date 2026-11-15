# WSL2 formalization against manuscript v59

Work in `/home/flengyel/src/CategoricalEssentialIncompleteness`.
Read `AGENTS.md`, `MANUSCRIPT_CURRENT.json`, `FORMALIZATION_STATUS_V59.md`
and `docs/V59_MANUSCRIPT_LEAN_CONTINUATION_2026-11-14.md`.

Version 59 corrects the bibliography publisher line break. All mathematical
text and all 77 numbered results and three definitions are unchanged from
v58. The reviewed v58 artifacts are retained. The Google report and its
assessment are in `docs/reviews/GOOGLE_V58_2026-11-14/`.

Theorem 5.3 is complete. The count remains 70 proved results and seven open:
8.9, 8.10, 9.6, 9.8, 10.7, 10.8 and 10.9. Lemma 8.9 is next. Preserve the
subobject-only initiality hypotheses, Boolean conventions and full extension
quantifiers. Preserve later local and remote work.

The positive-leaf assignment, primitive-recursive extraction and common finite
atom valuation are now constructed. See [the proof report](V59_SIGNED_DERIVATION_FINITE_SUPPORT_2026-11-14.md).
Continue with the formula valuation and internal truth invariant; Lemma 8.9
remains open. The new batch has incremental verification; the earlier full
replay remains separate evidence.

Use the existing serial build lock and pinned dependencies. Production
proofs and their dependencies must contain no proof placeholders; permitted
logical axioms are `propext`, `Quot.sound` and `Classical.choice`. The
designated isolated Palomar challenge declarations retain their exception.

Run from the repository root:

```bash
python3 scripts/test_verify_axiom_parser.py
python3 scripts/verify.py --manuscript-only
bash scripts/verify-wsl.sh
```

Record verification scope accurately. Commit completed changes to main and
push without force. Verify the live remote commit and current manuscript
version before reporting completion.
