# Codex continuation: numerical realization in the current manuscript

Complete Proposition 7.8 and its numerical syntax/proof comparisons next. Work from current main of `flengyel/CategoricalEssentialIncompleteness`; the active manuscript is now v48. This is a Lean task. The abstract revision changes no mathematical statement.

## Starting point

Read `AGENTS.md`, `MANUSCRIPT_CURRENT.json`, the correspondence file selected by that manifest, and `docs/CODEX_WSL2_CURRENT.txt`. Then read `manuscript/latex/sections/08c-numerical-realization.tex` and `08d-numerical-incompleteness.tex`, with their referenced definitions. Follow a later manuscript revision if main advances. The `V46` namespace is an implementation name, not a pinned verification target.

The reviewed source was main `c51c34d37df83ee9c568b7fe0ed92a801a3215c4`. Its latest full verification records proof commit `ff0363b8ec2fdad87cbdc3b3c53d8d0f614fd71f`: 965 successful commands, 1,274 retained and 13,290 current declarations in 497 production modules, with only `propext`, `Quot.sound`, and `Classical.choice`. The review is in `docs/reviews/V48_FORMALIZATION_REVIEW_2026-11-07.md`.

Reuse the existing WSL2 checkout and pinned dependencies. Inspect status, main, remotes, and worktrees before editing; reconcile newer work and preserve unrelated changes. Commit completed work to main and confirm the remote commit. No further permission is needed for this task.

## Preserve the completed arithmetic results

The reviewed sources support Proposition 7.5 and Theorem 7.6. In particular:

- `ArithmeticIndexedFibers.fiberInitial` is categorical slice initiality, and the individual/printed algebra comparisons and numeral-fiber pullback are constructed.
- `ArithmeticIndexedProvabilityFibers.printedProvability_numeral` concerns every internal sentence code in every PA model at an external numeral index.
- The uniform construction chooses one total source morphism before the index and consistency assumption. Its final theorem uses the actual axiom enumeration, actual native PA proofs, and the named sentence-code comparison.

Do not reopen 7.1–7.7 without an exhibited discrepancy or a dependency required by the next proof. Do not strengthen the final independence theorem to all nonstandard indices. Do not replace its one uniform morphism with a separate choice for each consistent extension.

## Primary batch: Proposition 7.8

Construct the numerical realization with the manuscript's definitions and quantifiers: variables `(1, ℕ)`, bounded arities including `d = 0`, recursive symbol carriers, every parameter object, and every axiom subobject of the sentence object. Axiom carriers may be c.e.; they need not be decidable.

Reuse the following existing results. Names below omit `CategoricalEssentialIncompleteness.V46`.

| Existing source | Use |
|---|---|
| `V46NumericalStableLists.lean` | `numericalEquivalence : TotalSplit 𝗧𝗔 ≌ NumericalTuples.Object`; `stableListAlgebra V`, including every parameter slice. |
| `V46ConcreteDecidableVariables.lean` | `ConcreteDecidableVariables.numerical`, also for finite judgement powers. |
| `V46SyntacticSyntaxPlainTotal.lean` | `SyntacticSyntax.mappedPlainPostfixData`: actual two-sorted syntax initiality and its parameterized initiality through an equivalence. |
| `V46SyntacticSyntaxOneSortInitial.lean`, `V46SyntacticSyntaxOneSortTotal.lean` | One-sort tree initiality and its use for arbitrary finite rule trees. |
| `V46SyntacticDerivationPolynomialComparison.lean` | Ordered constructor polynomial versus rule-labelled branches; `mappedInitial`. |
| `V46SyntacticDerivationSuccessComparisonCore.lean` | Natural isomorphism from successful validated trees to the actual `RulePresentation.inference` functor. |
| `V46SyntacticDerivationSliceInitial.lean`, `V46SyntacticDerivationAlgebraAdjunction.lean`, `V46SyntacticDerivationSuccessAdjunction.lean` | The slice/adjunction argument supplying categorical inference initiality. |
| `V46SyntacticDerivationTotal.lean` | Existing implementation of that argument for arbitrary rule presentations in the total splitting. |
| `V46FirstOrderTheory.lean` | `CategoricalSyntax.generated_firstOrder_theory`, once the actual initial derivation algebra has been constructed. |

A source-supported route is to compose
`(SyntacticPredicates.predicateEquivalence 𝗧𝗔).trans NumericalStableLists.numericalEquivalence`
and use `mappedPlainPostfixData` for the term/formula polynomials. Combine this with the existing numerical lists and decidable variables.

For derivations, apply the existing polynomial and successful-tree construction in `NumericalTuples.Object`. The interpretation family
`numericalEquivalence.inverse ⋙ (predicateEquivalence 𝗧𝗔).inverse ⋙ PredicateInterpretation.allModels 𝗧𝗔`
supplies a route to the preservation and conservativity hypotheses of `SuccessComparisonCore.comparison`. Discharge those hypotheses explicitly. Reuse the slice/adjunction argument; a second general transport framework is unnecessary unless an actual obstruction requires it.

This route has been checked against source signatures; resolve elaboration and universe constraints in Lean.

### Required endpoints

1. Construct the actual numerical term/formula algebra, lists, and a `CategoricalSyntax`. Prove initiality and parameterized initiality for every target algebra in each required slice. The fold retains the parameter and satisfies every constructor equation; uniqueness quantifies over all algebra morphisms.
2. Construct the actual typed finite-derivation algebra and prove its initiality for every finite rule presentation in scope. Target structure maps have partial-recursive realizers total on their carriers; do not require globally total recursive extensions, inhabited carriers, or an assumed evaluator with the desired equations.
3. Instantiate the existing logical schemes, generalization, and modus ponens for every axiom subobject. Derive the generated formula and sentence theories through the existing theorem.
4. Identify the transported carriers with the manuscript's literal named syntax and finite rule-labelled proof codes. Prove the constructor, free-variable, substitution/admissibility, and sentence-pullback comparisons that this identification requires. Preserve binder names.
5. Prove the printed arithmetic proof comparison: rule-label bijections preserve ordered premises and conclusions; inverse tree relabellings commute with conclusion; the interpreted regular image is the fixed `Prov_T` predicate. Prove the negation and numeral-substitution comparisons for these codes.

A carrier bijection alone does not prove the constructor, substitution, or proof diagrams. `ArithmeticSyntax.validSentenceCodes` uses the Foundation/Encodable presentation and is not definitionally the manuscript's named syntax. Reuse the existing comparison results and discharge any `AxiomsAdmissible` premise in the concrete application.

The manuscript's numeral one is zero-plus-one; Foundation's standard numeral one is the one constant. Reuse `ArithmeticNamedProofNumerals.translate_expandedNumeral`, `expandedNumeral_eq_standard_PA`, and `ArithmeticNamedProofTranslation.expanded_instance_substitution`. Equality of values or PA-provable equality of terms does not identify literal codes.

Tuple dimension also matters: `Tuple 0` is a unit and its code image is proper. Decode rule labels at the correct dimension before applying premise/conclusion maps.

Initiality transferred through the full standard theory proves categorical existence. It does not by itself prove a uniform computable index transformer for arbitrary indexed coefficient families; Proposition 7.8 does not require that additional assertion.

Keep the status row partial until its stated syntax, initiality, and coding comparisons are complete. A theorem whose premises contain the desired initiality or comparison does not discharge the row.

## Subsequent batch: cosheaf derivation initiality

After completing and verifying the numerical batch, the next bounded target is Proposition 9.3, followed by the identifications for 9.4 and 9.6. Keep these commits distinguishable from the numerical work.

The existing `ForkSyntax.fork_proof_presentation` and `t0_isLeast` already establish the coded conclusion-range properties. `ForkAxiomClosure.endpoint_axiom_extension_incomplete` already handles arbitrary c.e. axiom sets whose generated theorem sets extend an endpoint theory. The remaining problem is the actual initial-H presentation.

Use `RulePresentation` from `V46Inference.lean` with nullary rules `Ax = S² + S³ + S² + A + B`, no unary rules, and binary modus ponens indexed by `S²`. Construct the natural isomorphism to the printed `H(Q,q) = Ax + M(Q,q)`. Prove initiality in `E/S`, including the natural computable fold into every target slice algebra and uniqueness of every algebra morphism. Then identify its conclusion image and endpoints with the existing objects to recover 9.4 and 9.6.

`ForkProofTreeRecursion.fold_computable` assumes globally total constructor functions on an inhabited ambient type. That is insufficient for arbitrary numerical-carrier algebras. Also avoid evaluating every smaller proof code: invalid or unavailable atomic leaves can make such an evaluation diverge before it reaches a valid logical proof. Use evaluation of the selected tree or checked finite computation records.

Miller 8.1–8.6 remains a later construction. Its first endpoint must use one program with the same definedness and values for every representation of the sequence. Existing fixed-oracle approximation modules do not establish that endpoint.

## Checks and delivery

Add expanded statement checks at the intended types and include every production module in the current transitive axiom audit. Retain only the three permitted axioms. Universal statements must cover empty coefficients, nullary branches, and varying parameter families; finite examples cannot replace these quantifiers.

Use focused compilation while developing, then run the required full verifier through `bash scripts/verify-wsl.sh` after integration. Serialize full builds. Record the tested proof commit, exact input hashes, commands, exits, module inventory, and axiom union. Re-run checks only after relevant changes or failures.

Update the current correspondence table and implementation report with exact declarations and remaining obligations. Follow the manifest-selected manuscript throughout. Do not alter the approved abstract or manuscript mathematics to make a weaker Lean statement fit. Commit to main, confirm the remote, and deliver reports copied from the committed bytes.
