# WSL2 assignment for manuscript v79

Work in `/home/flengyel/src/CategoricalEssentialIncompleteness`. Fetch `origin/main` and integrate the active manuscript while preserving local work. Read `AGENTS.md`, `MANUSCRIPT_CURRENT.json`, the [v79 review](reviews/V79_PROOFS_AND_WSL_VERIFICATION.md) and the [active correspondence](../FORMALIZATION_STATUS_V79.md). The completed [v78 run](V78_WSL2_LEAN_VERIFICATION.md) tested `486414918381caf47688b1ae6574f1d9fe6e7b3a`. Its proof sources and machine-readable receipt are on main. The two comparisons below were still open at that commit.

1. In §6, construct the functor $\Pi_T$ with the manuscript's actual codomain of realized sets and typed numerical graph classes. Prove its hom maps are bijections, give essential surjectivity and identify the codings used on both sides. The existing equivalence with `NormalizedCategory T` has formal object terms in its target. State and check the comparison with that equivalence.
2. In §8.6, compare the observation functors for the same fixed-language theory presentations. For an asserted natural isomorphism, give its components and inverses, preservation of both supports in both directions, and the naturality square for every inclusion. The two existing evaluator lemmas have different inputs to the universal graph. Check any change of programs, numeral coding and transport of provability explicitly. If the claimed comparison fails, give the incompatible hypotheses or a counterexample and identify which printed results depend on it. Keep the proof of the printed functor distinct from the comparison with the other formal presentation.
3. Check the revised proof passages identified in the v79 review, including the Karoubi totality equation, the Boolean substitution induction at a binder, the finite selector in every PA model, both proof-search domains at the diagonal, the integer codes for the strict Miller bounds, and the two nullary axiom summands. Record the precise equality, quantifiers or hypotheses tested for each. Retain existing proofs where they suffice. Add strict statement checks where an inference lacks a matching check.

Update the active correspondence and integrate new declarations into the imports and statement and axiom audits. Commit the tested proof and correspondence inputs before the full run. Use the pinned toolchain and dependencies. Run the targeted strict Lean commands and then the following from the repository root.

```bash
python3 scripts/test_verify_axiom_parser.py
python3 scripts/verify.py --manuscript-only
bash scripts/verify-wsl.sh
```

Report the exact tested SHA, commands, exit codes, machine-readable evidence and any unresolved claim in `docs/V79_WSL2_LEAN_VERIFICATION.md`. A successful run establishes the declarations present at the tested commit. Record separately which manuscript comparisons each declaration proves. Commit and push the proof sources, correspondence and report to `origin/main` without force, fetch again, and compare the tested inputs with the fetched copies. Return the tested SHA, fetched main SHA, report link and any remaining mathematical obligation to the manuscript chat. Palomar registration is a separate author decision.
