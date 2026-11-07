# Author-side review of the syntax and soundness continuation

Scope: the numerical source/check batch after main `2e7152b`, with the
manifest-selected v48 target, its imports, correspondence and verification
records. The 7.1–7.7 proofs and earlier v47 verification remain preserved.
Codex made no manuscript changes. The independent v48 review inspected
`c51c34d` and recorded evidence; it did not independently rerun Lean.
This author-side record covers the changed endpoints and does not certify
whole-manuscript completion or an independent kernel run.

## Current numerical batch and remaining blocker

The constructed numerical term/formula and list algebras are identified
with the actual unary named-word carriers by constructor-preserving
algebra isomorphisms; initiality includes every parameter slice. Arbitrary
finite rule data have an initial inference algebra with each child's own
prescribed conclusion, including nullary rules and empty coefficients.
Native decoding, full Option-valued substitution, independent admissibility,
free-variable lists and the sentence pullback have expanded checked types.
The arithmetic negation and numeral-substitution morphisms now use that
constructed syntax, with exact zero/add-one words and the canonical PA
standard interpretation. Formula-coordinate changes conserve original
proof words; rule-coefficient isomorphisms induce inverse initial folds
with constructor, conclusion, label and ordered-child equations.

Proposition 7.8 is still partial. The actual arithmetic rho_n, the full
PA-to-numerical derivation-algebra comparison and rho_T, and the fixed
Prov_Gamma image are open. The intermediate PA proof-image comparison
is not treated as the final numerical image theorem. No evaluator,
carrier bijection or assumed comparison discharges these dependencies.

## (A) Kill-shots / hard blockers

No mathematical counterexample or confirmed hypothesis drift was found in
the inspected new endpoints. Initiality in 5.5/5.8 remains the full universal
property for the manuscript polynomial, arbitrary parameter families and
original typed rule pullbacks. The new native algorithm/categorical fold
comparison, success pullback, standard soundness factor and arithmetic
ultrapower instance are proved with their intended effective hypotheses.
The application dependencies below still prevent a whole-current-manuscript completion claim.

## (B) Major weaknesses

1. **The indexed-family fiber universal property is proved.** Anchor:
   `prop:arithmetic-theory-fibers`. The actual indexed coefficient, full-family
   initial algebra and parameter-preserving ordered rules are retained.
   `ArithmeticIndexedFibers.sliceEquivalence`, `numeralInferenceComparison`
   and `algebraEquivalence` derive the extensive decomposition from actual
   constructor coefficient pullbacks. `fiberInitial` covers every algebra
   morphism; `individualFiberAlgebraIso`, `sentence_pullback` and
   `sentenceTheory_fiber` prove the per-e derivation and sentence/image
   comparisons. `individual_oldGamma_comparison` and
   `individual_oldGamma_model` identify the original named Γ_e calculus and
   its literal theorem predicate. The fiber universal property is established
   by these comparisons, rather than inferred from full-family initiality
   alone.

   The printed presentations are also compared. The source and realized
   `ArithmeticIndexedAxioms.Exponential.mono_square`/`realized_square`
   identify the exponential-pair axiom coefficient. The product predicate D has the proved chart J(D)≅E×S.
   The proof presentation isomorphism identifies J(P₀) with the sentence
   derivation object P; `printedConclusion_realization` proves
   J(γ_c)=v⁻¹cu for the actual γ_c:P₀→D. The selected program has PA-proved
   graph and exact domain, and `sentence_range_regular_image` gives the
   actual range/image splitting. `printedProvability_numeral_PA` proves
   ∀z, Prov(ē,z) ↔ Prov_Γe(z) for every external numeral e; its model
   theorem holds at every internal word of every PA model. A separate
   representation or axiom-correctness premise is not required.

2. **The concrete arithmetic proof-system comparison is now proved.**
   `ArithmeticNamedAxiomComparison.axiomsAdmissible_PA` discharges the
   source-axiom premise from the actual native PA arithmetic/order and
   arbitrary-induction axioms with finite universal closure. The proved
   numeral-convention transport and native finite-proof realization yield
   the standard Γ bounds. Their fixed universal closures transfer to every
   M≡N, and `ArithmeticDiagonalRepresentation.printed_representation`
   proves the proper sentence-object inequalities of 7.1. The semantic
   model K is constructed from native consistency; its actual soundness
   factor and ultrapower transport discharge the target consistency
   conditions. `ArithmeticInternalComparison.internal_comparison` and
   `total_undecidable_family` prove the categorical 7.3 application and its
   total source family. No source-admissibility, assumed soundness factor,
   PA consistency proof or imported arithmetic incompleteness theorem is
   used as a replacement for these steps.

3. **The uniform sentence theorem 7.6 is proved.** The chosen Σ₁ PA
   enumeration has the exact native standard-code characterization
   `ArithmeticIndexedPAEnumeration.axiomCodes_standard`; actual induction
   substitution and finite named universal closure are included.
   `fiber_extendsPA` supplies the PA-extension premise for every Γ_e.
   `ArithmeticUniformIndependent.uniform_independent_sentence_codes` and
   `uniform_independent_sentences` use one actual total q:E→S, constructed
   before e or its consistency proof. At each standard externally consistent
   fiber, q(ē) has a closed named formula code outside the actual theorem
   image and negation preimage, and neither that formula nor its negation
   has a native proof. Local evidence disjointness and the diagonal bounds
   are derived. The final theorem has ordinary per-fiber consistency only;
   it has no residual hRep, hAx, soundness or semantic-model field. Its
   independence assertion uses N. The all-PA-model numeral-Prov statement
   above is a distinct presentation theorem.

4. **Later applications remain separate.** The first open principal
   obligation is 7.8: parameter-stable named syntax and finite-inference
   realization in the numerical tuple category, with the specified syntax
   and proof-code comparisons. Miller representation independence and
   cosheaf derivation initiality remain later obligations. Numerical tuple
   comparison 7.7 is proved; rows 9.1 and B.10 retain their corrected wording.

The direct Corollary 7.4 application is also proved: an actual recursive
Θ-preimage and partial source conditional contradict categorical Corollary
3.2; the c.e. parallel-enumeration proof and native finite axiom replacement
give closed-sentence and extension incompleteness. Its final statement
contains only the printed Γ PA-derivability and consistency hypotheses.

## (C) Minor issues

**Elaboration dependencies were repaired without changing mathematics.**
Local notation in concrete `variable` declarations hid dependencies on
signature parameters and semantic operations, producing apparent graph-type
normalization failures. Fully written dependent binder types and explicit
section-variable inclusion resolve the concrete soundness construction.
Abstract model-predicate lemmas expose raw graph conditions through proved
iff statements and have literal algebra/carrier/conclusion equalities to the
existing generated-theory data. They do not supply an assumed evaluator,
initiality or soundness factor. Targeted diagnostics and all failed
snapshots/logs are preserved. The production proofs use the existing strict checker and permitted-axiom audit.

**The indexed proof layers have targeted kernel evidence.** The numeral
split stores maps together with generically proved primitive and copair
laws. Its checked opaque body constructs those laws; it does not postulate
them. The inference comparisons derive from original ordered-premise and
conclusion diagrams, and the actual Γ_e comparison is an algebra isomorphism.
All 60 new production/check files have passed their targeted production and
strict checks. The existing continuation report lists the component receipts:
`native-fibers-FROZEN.json`, `V46ArithmeticIndexedPAEnumeration-FROZEN.json`,
`V46ArithmeticIndexedExponential-FROZEN.json`,
`V46ArithmeticIndexedProvability-FROZEN.json` and the uniform component of
`first-order-bridge-freeze.json`. Optional expanded-chart drafts and failed
elaboration snapshots remain preserved separately. Full integrated
verification passed as recorded below.

The new realization comparison is proved for arbitrary T extending PA,
predicate codomain and T-supported, T-total graph, before specialization to
the arithmetic formula. Explicitly typed predicate objects preserve the
original carrier. Reduced diagnostic limits exposed elaboration problems;
no production limit was raised. The literal Total sentence morphism has its
actual all-PA-model graph and value comparison. Its additional expanded
source-projection drafts remain preserved and are not used as a substitute
for a proved equation.

## (D) Cross-section consistency

- The original named polynomial, labels, ordered children and parameter
  families are preserved. Arbitrary algebra operations require their actual
  T-supported total graphs, not primitive-recursive or PA-total operations.
  Initiality adds no consistency, c.e., soundness or standardness hypothesis.
- The actual computed substitution is a proved algebra morphism; stable
  initiality identifies it with the fold. Its success pullback is identified
  with the independent free-for recursion. The equal-binder branch keeps the
  original body even if recursive substitution fails.
- Every rule child has its own prescribed conclusion; the parent conclusion
  is induced by the rule's conclusion map. Nullary rules need no global
  formula point. Standard reverse finite-tree comparison requires N models T;
  no nonstandard Set initiality is asserted.
- Formula-image/sentence/source-idempotent assembly uses the constructed
  syntax, lists and arbitrary-rule initiality. Chosen pullback and inverse
  equivalence codes are not assumed to be original formula codes or primitive
  recursive charts.
- Standard soundness uses the actual seven parameter families, both rules,
  constructed derivation induction, actual sentence pullback and unique
  validity corestriction. Only nonlogical axiom validity is assumed.
  Semantic K and arithmetic code models N/M remain distinct; disjointness
  retains nonempty K.
- The arithmetic-ultrapower instance supplies the proved standard factor and
  the constructed canonical comparison. It derives factorization and
  conclusion-image consistency, rather than assuming a comparison or factor.
- Exponential/parity object coding and the uniform computation comparison are
  separate completed proofs. Native comp/s certificates accompany full
  all-internal PA graph laws; k_e is an actual PA-total program. Production
  graph equality is proved in PA at fixed external indices on all internal
  inputs, with no arbitrary-index stage-persistence assumption.
- The indexed parameter e is standard when a numeral fiber is selected;
  the printed Prov comparison quantifies over every internal word of every
  PA model. The exact chosen PA-axiom code characterization and final native
  independence theorem concern N. External Γ_e consistency supplies neither
  a PA consistency proof nor a nonstandard consistency assertion.
- The printed exponential pair is compared with the intermediate raw pair
  presentation, including the restricted axiom coefficient, proof carrier
  and selected conclusion program. These are proved morphism/graph
  comparisons, rather than identifications of arbitrary chosen codes.

## (E) Verification and disposition

The baseline full verification exited 0 in `.codex-work/verify-20261106T052422Z-MLM1qM`; all 837 commands passed.
The permitted axiom union and clean pinned dependencies were checked. All
1119 tested input hashes match proof commit `16ec62198d0aaa6506fc50d949f35af0fb26d94d`, whose ordinary
main push and remote ref were confirmed. The delivery receipt records the
separate report commit and six copied-byte hashes.

The completed core-baseline full verification exited 0 in
`.codex-work/verify-20261106T125901Z-Acu0zJ`; all 905 commands passed.
The permitted axiom union and clean pinned dependencies were checked. All
1187 tested input hashes match proof commit `e08d21c7eee33e6e7ee398411124039133a92905`, whose ordinary
main push and remote ref were confirmed. The delivery receipt records the
separate report commit and six copied-byte hashes.

Report commit `1db7a66` preserves the completed e08d21c core baseline and
its committed-byte delivery; it predates this indexed proof batch.

The final concrete specialization is `ArithmeticIndexedPrintedFamily`: its coefficient data use the proved realized axiom square, its printed algebra is constructed by arbitrary-rule initiality, and its algebra isomorphism preserves the constructors and conclusion. The actual numeral fibers and sentence images are proved. Its P₀ presentation and conclusion equation identify the existing selected program with that printed initial algebra.

Full v48 verification exited 0 in `.codex-work/verify-20261107T141721Z-5BSDgL`;
all 1083 commands passed. The three permitted axioms and clean
pinned dependencies were checked. All 1365 tested input hashes
match proof commit `35398e4874e333fa31756a28f5ddfd2ab68b0b1a`, whose ordinary main push
and remote ref were confirmed. Proposition 7.8 remains partial at the
concrete arithmetic comparisons described above. The delivery receipt
records the report commit and all six copied-byte hashes.

An earlier full replay returned exit 1 only after the 905 successful Lean
commands: the lexical gate matched an English word in a documentation
comment. The comment-only repair and complete successful rerun are recorded;
no proof, statement, axiom or verifier condition was relaxed.

The scoped source/type review supports the stated completed endpoints and
explicit remaining obligations. It does not replace the kernel/axiom checks,
certify the whole current manuscript or revise the manuscript to weaken the target statements.
