# Syntax, substitution and coding continuation — 2026-11-05 (UTC)

The verified continuation adds 112 Lean source/check files
(10,786 lines), with explicit manuscript-type checks and dynamic
transitive axiom coverage. The prior proof files, dependency pins and
manuscript v46 remain unchanged. The tested proof commit is `e194c3f4510b3605aea8975383ab060d50b1890f`;
ordinary `git push origin main` succeeded and the remote ref was confirmed
at that commit. The delivery receipt records the subsequent report commit.

## Completed mathematics

Declaration prefixes below abbreviate `CategoricalEssentialIncompleteness.V46`.
The manuscript entry point is `manuscript/latex/main.tex`. These are the
completed results of this continuation; the remaining v46 obligations
are listed below.

| Manuscript dependency | Completed declarations and concrete content |
| --- | --- |
| Appendix A.3, absent-variable substitution | `CategoricalSyntax.term_substitution_absent`, `formula_substitution_absent`, `termAbsent_fixed`, `formulaAbsent_success`, `formulaAbsentAdmissible`: actual false-membership fibers and formula admissibility lift, for arbitrary generalized elements under the original categorical syntax assumptions. |
| Appendix A.1, Boolean products and variables | `BooleanSquare.iso` constructs the four-summand isomorphism to the genuine binary product of Two. `SyntacticDecidableVariables.decidableVariables`, `ConcreteDecidableVariables.total`, `numerical` and `DecidableVariables.Transport.mapped` construct the diagonal pullback for every represented variable object and transport it to total-split and numerical categories. |
| §5 object coding | `ExponentialPairing.total_PA`, `inverse_PA`, `code_primrec`, `first_primrec`, `second_primrec`, `projections_PA`: printed exponential pairing, internal inverse equations, and separate standard primitive-recursive certificates. `ExponentialProducts.rawProductIso` and `productIso` are actual T-provably total inverse translations for arbitrary Σ₁ carriers. |
| §5 formal-object and model comparison | `PrintedObjectCoding.isoToOmega`, `equivalence`, `homProgramEquiv`, `preserves_restrictions`; `value_model`, `value_bijective`, `valueEquiv`, `comparison_model`: same formal labels, full numerical quotient-program homs, recursive gamma with exponential products and even/odd sums, and exact graph correspondence at every model element. |
| Proposition 5.5 dependencies | `SyntacticSyntax.decode`, `fiberRepresentation_existsUnique`, `encodePolynomial`, `postfixAlgebra`, parser constructor/framing laws, positive finite value records, `SliceAlgebra.evaluation_existsUnique`, `evaluationMorphism`, `evaluation_over`, `termFold`, `formulaFold`: arbitrary actual algebras in every predicate-category parameter slice now have actual unique accepted-word evaluators and over-parameter arrows. Constructor Hom laws and initiality remain open. |
| Parameter transport | `SyntaxPolynomialTransport.naturalIso`, `algebraEquivalence`, and the syntax terminal-parameter comparison construct actual polynomial/algebra equivalences. `terminalMappedAlgebra_eq` identifies the transported structure by reflexivity; `initialOfTerminalParameters` reflects initiality to the base category. |
| Lemma 5.8 dependencies | `SyntacticDerivation.finitePowerEncoder`, `tupleMorphism_compatibility`, `original_isPullback`, `ruleInputIso`, `ruleInputIso_conclusion`: ordered finite-power coding and the actual original H_R input pullback with its conclusion equation. Positive finite-record nil/cons/singleton laws and PA conditional run functionality are proved. |
| Proposition 7.8 list fragment | `NumericalStableLists.numericalEquivalence`, `stableListAlgebra`: stable list algebras for every numerical coefficient object and every parameter, via the standard true theory and actual numerical tuple equivalence. |
| Appendix B.2/B.3 | `RegularEquivalence.regularEpi_iff`, `regular`; `NumericalForkPartialMaps.Diagram`, `diagramRegular`, `diagramFinitaryExtensive`, `equivalence`, `span_pullback_range`; `ForkRangeStability.partial_range_stable`: regular/extensive literal numerical diagrams, ordinary monic-span comparison, and range stability for one selected span under every total base change. |

Syntactic results assume T extends PA; they do not require T to be
consistent, computably enumerable or sound. Pairing/inverse equations and
the conditional record laws hold in arbitrary PA models, including nonstandard elements. Decoded algebra evaluation uses
its T-provable support and totality and is interpreted in M satisfying T.
The model statements' explicit PA-model instance follows from M satisfying
T. Generic categorical substitution and transport retain their stated
regular/extensive or finite-limit/coproduct hypotheses and arbitrary
universes. Decidable variable equality does not assert decidable
membership of arbitrary Σ₁ predicates.

Numerical stable lists concern ordinary computable totality. The
categorical equivalence uses external choices and does not supply a
uniform computable index transformer for arbitrary indexed algebras.
Additional fork restriction structures are checked in the coded fork
presentation; the literal monic-span equivalence explicitly preserves
restrictions and ranges.

## Drift and verification

The starting checkout was clean at `0c7fdc79e26cf0f7da360a4c84f2773b1ad12b3a`.
All 404 inputs matched the previous successful full verification, which
was reused as the baseline. Of those inputs, only the combined entry
point and v46 statement-audit import lists changed. All prior proof-file,
source-pin and toolchain bytes remain unchanged. Every new production
module and Checks module is imported; no audited declaration was removed.
The combined-import instance-name collision in the new Sorts module was
repaired and reverified without changing its theorem statements.
The first complete run executed all 263 Lean commands successfully but
exited 1 when the final source-token scan matched the ordinary English
word `admit` in an Evaluation documentation comment. That wording was
changed to `have`, with no proof, definition or verifier change. The failed
run is preserved at `.codex-work/verify-20261105T023248Z-cc9gvs`; the
complete verifier was then rerun on the corrected source.

Final command: `bash scripts/verify-wsl.sh`, invoking
`LEAN_NUM_THREADS=1 python3 scripts/verify.py`; exit **0**.
The run is `.codex-work/verify-20261105T031256Z-jtQgZR`. All 263 recorded
commands passed, including the combined build, retained v5 audit,
expanded v46 statement audit, strict v46 source checks and transitive
axiom audit. The audit covered 1274 retained declarations
and 4724 v46 declarations in
135 production modules. The axiom union is
`propext`, `Quot.sound`, `Classical.choice`.

Lean is pinned to `v4.35.0-rc2`, compiler
`11acb17ec6b07a8f9e9173e6845197929540936b`; Mathlib to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; Foundation to
`01f617fbe240a84aaf1c45b31b9d65e0a2e21c1d`.
All 16 dependency revisions,
356 imported source pins and
24 v46 manuscript files passed their checks.
Every one of the 516 tested integration inputs
was compared to `git show` at the proof commit. The source-snapshot
SHA-256 is `9c92ef0cf86c226adbb3a8ddd03fa1d74eb056e245cb3f3adaf7ac2037f8a2d9`.

The [verification JSON](V46_SYNTAX_CONTINUATION_VERIFICATION_2026-11-05.json) records every
command, status, dependency and source hash. The
[author-side review](reviews/V46_SYNTAX_CONTINUATION_REVIEW_2026-11-05.md),
[writing review](reviews/V46_SYNTAX_CONTINUATION_WRITING_2026-11-05.md) and
[source manifest](reviews/V46_SYNTAX_CONTINUATION_SOURCE_SHA256_2026-11-05.txt)
give the review scope and remaining limitations. No independent kernel,
registry verification, manuscript PDF compilation or whole-paper
certification is claimed.

## Remaining obligations and delivery

The printed uniform trace comparison in 5.1 remains open. Proposition
5.5 still needs plain-parser conservation/decomposition, constructor
commutation, uniqueness, predicate-slice initiality and final TotalSplit
syntax transport. The separate
standard `Nat.Primrec` parser certificate has not been exported.

Named-variable syntax/substitution comparison (5.7), finite-derivation
initiality and proof-presentation comparison (5.8/5.9), concrete model-local
semantic substitution and soundness, and the Γ-instance categorical
arithmetic chain remain. Fixed standard parameter-free B_T graphs do not
by themselves cover C(M) with arbitrary nonstandard indices or model
parameters. Uniform indexed families, numerical inference realization,
Miller representation independence and cosheaf H-initiality remain as
specified in [the correspondence table](../FORMALIZATION_STATUS_V46.md).
Ignored continuation drafts and logs of failed elaborations remain
preserved and are not counted as completed proofs.

The active Windows profile and existing Downloads known folder were
queried directly: `C:\Users\fleng\Downloads`
(`/mnt/c/Users/fleng/Downloads`). Delivery uses a dated, final-report-commit
suffix directory and six files extracted from committed bytes: this
report, verification JSON, correspondence table, both review reports and
source manifest. `DELIVERY_SHA256.json` records the final synchronized
commit, exact destinations, byte counts and copy hashes. Its verified
receipt is required before reporting delivery complete.
