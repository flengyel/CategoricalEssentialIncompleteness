# Syntax and derivation initiality continuation — 2026-11-05 (UTC)

The new proofs establish Proposition 5.5's parameter-stable syntax initiality
and Lemma 5.8's arbitrary-rule derivation initiality in the production
syntactic category and its total restriction splitting. Both results use
constructed carriers, constructors and folds. No evaluator or initiality
conclusion is an input assumption. The manuscript remains v46, and its
uniform computation-presentation comparison remains the separate 5.1 obligation.

This record continues the verified proof commit
`e194c3f4510b3605aea8975383ab060d50b1890f` and reviewed report commit
`3f53b33d647940d0429679db192f3ea689b8a5d4`. The existing verification JSON
records the tested source bytes, integration run, subsequent proof commit and
push. Previous committed records and ignored failed-elaboration logs remain
available; this is the same implementation record, updated for the new results.

## Completed mathematics

Declaration prefixes below abbreviate `CategoricalEssentialIncompleteness.V46`.
The manuscript entry point is `manuscript/latex/main.tex`.

| Manuscript result or dependency | Completed declarations and content |
| --- | --- |
| Proposition 5.5: constructor-compatible fold | `SyntacticSyntax.termFold_commutes`, `formulaFold_commutes`, `foldHom`: the actual finite-record evaluator commutes with every constructor and gives an algebra morphism to every actual algebra in every predicate-category parameter slice. |
| Proposition 5.5: universal property | `SyntacticSyntax.foldHom_unique`, `withParametersInitial`, `postfixInitial`, `categoricalSyntax`: an arbitrary algebra morphism's constructor equations imply equality with the constructed fold. Internal node-count induction covers nonstandard lengths; joint faithfulness gives T-provable morphism equality. |
| Proposition 5.5: literal parser comparison | `SyntacticSyntax.Postfix.carrier_iff_singleton`, `carrier_plain_pa`, `carrier_plain_theory`, `plainCarrierIso`, `plain_constructor_comparison`: conservation identifies plain singleton acceptance with the stored-word check on the same literal word. Ordered root decomposition, guarded constructor injectivity, sort disjointness and strict child-size decrease are proved. |
| Proposition 5.5: plain syntax and total splitting | `SyntacticSyntax.plainPostfixInitial`, `plainWithParametersInitial`, `plainCategoricalSyntax`, `totalCategoricalSyntax`, `plainTotalCategoricalSyntax`: actual constructor-preserving algebra isomorphisms and polynomial/slice comparisons transport initiality, including every parameter and arbitrary target families, to `TotalSplit T`. |
| Proposition 5.5: standard primitive-recursive parser | `SyntacticSyntax.NatVectors.run_natPrimrec`: for every fixed pair of signature polynomials, the actual `Postfix.run` on N is primitive recursive jointly in the word and initial stack. The separate vector/recursion closure and packing certificates are constructed. This concerns structural parsing; arbitrary coefficient-predicate membership is not asserted decidable or primitive recursive. |
| Lemma 5.8: original inference functor | `SyntacticDerivation.PolynomialComparison.comparison`, `injection_comparison`, `SuccessComparison.comparison`: labelled ordered tree constructors are compared with the finite rule coproduct, then the validator's success pullback is compared with the original inference functor. Each component uses `R_n ×_(F^n) Z^n`; child conclusions match their prescribed premises, and the parent conclusion is induced by `q_n`. |
| Lemma 5.8: predicate category | `SyntacticDerivation.derivationCarrier`, `derivationConclusion`, `derivationAlgebra`, `derivationInitial`, `derivationConstructor_tree`, `derivationFold_conclusion`, `derivationFold_constructor`, `derivationFold_unique`, `nullaryDerivation`: actual finite derivation codes, conclusion, constructor equations and unique folds for arbitrary finite rule data. |
| Lemma 5.8: actual total split category | `SyntacticDerivation.totalDerivationCarrier`, `totalDerivationConclusion`, `totalDerivationAlgebra`, `totalDerivationInitial`, `totalDerivationConstructor_tree`, `totalDerivationFold_conclusion`, `totalDerivationFold_constructor`, `totalDerivationFold_unique`, `totalNullaryDerivation`: the same universal property for every actual `TotalSplit` formula object and rule presentation, with the original premise pullbacks. |
| Generated-theory dependencies | `SyntacticSentenceImages.sentenceImageIso`, `theorySplittingIso`; `SyntacticSentenceImages.sentenceGraph_functional_pa`, `sentenceIndex_uniform_pa`, `sentenceProgram_range_literal`, `programTheorySplittingIso`: actual sentence-image charts, filtered program graphs and representing source restriction idempotents. Their sentence predicate is the formula-coordinate image of the actual sentence inclusion; its numerical FV=0 identification still requires 5.7. |
| Lemma 5.1: completed trace fragments | `UniformTrace.functionality_PA`, `universal_PA`, `section_PA`, `stage_totality_PA`, `trace_comparison_PA`, `out_natPrimrec`: uniform functionality, exponential-input universal evaluation, fixed-index agreement with production, all-internal-index fixed-stage totality, and an actual existential trace/output comparison. The exported trace predicate is presently Sigma-one; its primitive-recursive certificate and uniform composition/specialization/index equations remain open. |
| Semantic dependencies | `NamedFiniteSyntax.Term.evaluate_substitute`, `Formula.substitute_isSome_iff`; `Formula.holds_congr`, `holds_substitute`, the seven `valid_*` scheme lemmas, modus ponens/generalization and validity-negation disjointness: proved on external literal named finite trees. `NamedPostfixEncoding` constructs their actual standard postfix encoder, carrier preservation and root/input equations; `NamedPostfixData` proves ordered payload decomposition and injectivity. Full decoding/bijection and the numerical substitution comparison remain required before claiming realized 6.5 or coded 6.6. |

The syntax and derivation results assume only that T extends PA. Coefficient
objects, the finite arity bound and parameters are arbitrary. Target families
and algebra operations are arbitrary actual morphisms with T-proved support
and totality. They need not be primitive recursive or PA-provably total.
Consistency, computable enumerability, soundness and standardness of T are
not assumptions.

The manuscript polynomial is retained:
`K(X,Y) = (V + sum Sigma_k × X^k,
X^2 + sum Pi_k × X^k + Y + Y^2 + V × Y)`.
Variable names and ordered children remain literal syntax data. Carrier
membership, evaluation records and conclusion/validation witnesses are
existential witnesses. The derivation carrier retains the original tree code
as its sole code field. Its comparison with the chosen success pullback is
an actual algebra isomorphism preserving the tree inclusion and conclusion.
Nullary rules do not require a global point of the formula object.

The derivation proof uses the constructed ordinary rule-tree initial algebra,
a total Option(F) validator, its proved success/inference natural isomorphism,
and a proved algebra adjunction. The final initiality theorem has no assumed
inference initiality or evaluator field. The model proofs retain interpreted
terminal-fiber points; they do not identify different child judgements with
the parent's judgement.

The external semantic lemmas concern finite trees and standard arithmetic
codes. Their semantic structure K is distinct from the arithmetic code model.
Validity-negation disjointness uses a nonempty semantic structure. No assertion
identifies arbitrary nonstandard model words with external finite trees or
asserts initiality among all Set operations in such a model.

## Drift, verification and delivery

The starting checkout was clean at `3f53b33`. All 516 inputs matched the last
successful full run, so its baseline was reused: 263 successful commands,
1,274 retained and 4,724 v46 declarations, with only `propext`, `Quot.sound`
and `Classical.choice`. Its source-snapshot hash was
`9c92ef0cf86c226adbb3a8ddd03fa1d74eb056e245cb3f3adaf7ac2037f8a2d9`.

Preflight for this integration found 639 inputs. Among the existing inputs,
only the combined entry, statement-audit import lists and verifier changed;
123 Lean source/check files were added. Every new file is directly imported.
Prior proof sources, the pinned toolchain, imported-source pins, dependency
revisions and manuscript v46 remain unchanged. Unrelated work and ignored
continuation drafts and failed logs have been preserved.

The existing verifier now records dependency revisions and worktree status
before building and after the axiom audit. It rejects tracked or untracked
dependency edits and preserves them. A temporary Git fixture checked clean
acceptance, tracked/untracked rejection, exact edit preservation and revision
mismatch rejection; all 16 actual pinned dependency worktrees were clean.
This extends the existing verifier rather than adding a verification framework.

The required full command `bash scripts/verify-wsl.sh` passed with exit **0**,
under the existing lock with `LEAN_NUM_THREADS=1`. Run:
`.codex-work/verify-20261105T082552Z-2Hh2l8`. All 386 commands passed, including the
combined build, both statement audits, strict sources and transitive axioms.
The audit retained all 1,274 earlier declarations and covered
6,143 v46 declarations in 197 production modules;
the axiom union is `propext`, `Quot.sound`, `Classical.choice`. All 16 dependency
worktrees were clean at start/end, 356 imported pins and
24 v46 manuscript files passed. All
639 tested inputs matched `git show` at proof commit
`54a5905ac392469b5e78ec1232a64952d85df942`; its ordinary main push and remote ref were confirmed.
Source-snapshot SHA-256:
`f27917912324e1441cf25533a3307d39a3d16a29eb66ccd6910b707b412487a4`. The final report commit and copied-byte receipt
are recorded by the existing delivery procedure.

Lean remains pinned to `v4.35.0-rc2`, compiler
`11acb17ec6b07a8f9e9173e6845197929540936b`; Mathlib to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; Foundation to
`01f617fbe240a84aaf1c45b31b9d65e0a2e21c1d`.
The independent review of `3f53b33` inspected source and recorded evidence;
it did not independently rerun Lean or certify completion of v46. The new
source reviews are scoped author-side/collaborating-agent reviews.

## Remaining mathematical dependencies

The exact 5.1 remainder is the primitive-recursive trace predicate and its
PA defining-graph comparison, uniform composition and specialization for
arbitrary internal indices/parameters, and PA-provably total parameter-index
programs. Completed exponential/parity object coding is separate.

Proposition 5.7 still needs the actual PA-verified numerical list/FV and
substitution traversals, their primitive-recursive certificates and comparison
with the categorical folds and free-for success domain. The equal-binder
branch must retain the original body even when its recursive result fails.
Theorem 5.9 still needs those numerical formula/sentence identifications and
the final concrete generated-theory assembly; the checked image/range helpers
do not by themselves supply the FV=0 identification.

The next semantic dependencies are the standard named-code bijection and
algorithm comparison for 6.5, then soundness of the constructed coded
schemes/rules and the actual unique validity factorization/disjointness for
6.6. Only that proved factorization can instantiate the existing arithmetic
ultrapower transport in 6.9. Sections 7.1–7.3 retain the generated Gamma
predicates, diagonal bounds, partial proof-search lift and categorical
comparison application. An imported arithmetic incompleteness theorem does
not replace that application; external consistency is not a PA proof of
consistency. Model scope, nonstandard inputs and model parameters remain
explicit obligations.

Indexed families, numerical inference realization, Miller representation
independence and cosheaf derivation initiality remain later work. The stale
9.1/B.10 wording about the completed numerical tuple comparison is corrected.
Manuscript prose revisions remain deferred.

Delivery reuses the existing Windows Downloads procedure at
`C:\Users\fleng\Downloads` (`/mnt/c/Users/fleng/Downloads`). Six useful records
are extracted from committed bytes into a new commit-suffixed directory;
differing existing files are preserved. `DELIVERY_SHA256.json` records the
confirmed remote commit, destinations, byte counts and verified copy hashes.
