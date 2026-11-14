# Lean correspondence review of manuscript v57

Pinned repository: `flengyel/CategoricalEssentialIncompleteness`, commit `dfe6d3b9b948875d9d268ef8bbd332d65c6b53e5`.

The current correspondence table records **69 proved numbered counterparts and eight open numbered obligations**. Its arithmetic is consistent: the 62 retained results plus seven completed additions (4.4–4.8, 5.1–5.2) give 69; 5.3, 8.9, 8.10, 9.6, 9.8, 10.7, 10.8 and 10.9 remain open. The table has exactly 77 result rows. Three numbered definitions are outside that count.

No mismatch was found between the seven completed additions' principal declarations and their printed hypotheses and conclusions in the source and statement checks examined. This is a source-level correspondence audit, with a separate assessment of the recorded verification evidence. It is not a new Lean kernel build or an independent reconstruction of all 62 retained formalizations.

## Coverage outline

| Printed result | Current status | Assessment |
|---|---|---|
| 4.4 Generation reflection | Proved | Principal reflector uses initiality only for axiom subobjects. Arbitrary presentations first pass through their regular image. |
| 4.5 Translation Galois connection | Proved | Translation structure, inverse closure, adjunction, generation identity, composition, and reflection across presentations have declarations and checks. |
| 4.6 Comparison of deduction | Proved | Both squares, natural comparison, restricted right adjoint, pullback construction and rule-transposition construction are present. |
| 4.7 Free first-order adjunction | Proved | Pair and theory categories, both functors, natural hom equivalence, unit and counit are constructed. |
| 4.8 Incompleteness–inseparability equivalence | Proved | Both directions, Boolean completion and restriction-idempotent/subobject comparison are implemented. |
| 5.1 Partial-slice Turing structure | Proved | Actual partial slices, full constant-object recursion subcategory and restriction-preserving splitting equivalence are checked. |
| 5.2 Theory extensions | Proved | Actual span postcomposition and pullback, both adjunctions, properness, comparison square and subobject inequality are checked. |
| 5.3 Associated incompleteness | Partial; open | Retraction and Boolean equivalences are proved. Transfer of closed theories and full essential-incompleteness equivalence remain open. |
| 8.9 Arithmetic signed theory | Open | No completed finite-positive-label consistency proof or final specialization is claimed. |
| 8.10 Arithmetic associated categories | Open | Depends on 8.9 and remaining 5.3 transfer. |
| 9.6 Miller parameterized deduction | Open | Existing syntax and base derivation initiality do not yet establish the printed every-parameter derivation theorem. |
| 9.8 Miller associated categories | Open | Depends on 9.6 and remaining 5.3 transfer. |
| 10.7 Fork first-order realization | Open | Existing propositional fork folds do not establish first-order syntax and derivations in every parameter slice. |
| 10.8 Fork conservativity | Open | Natural first-order embedding/erasure and the resulting comparison remain open. |
| 10.9 Fork associated theories | Open | Depends on 10.7–10.8 and remaining 5.3 transfer. |

## Principal correspondence findings

### 4.4: the previous hypothesis discrepancy is repaired

`V46FirstOrderReflection.lean` declares
`proofs : (A : Subobject S) → Algebra (... A.arrow ...)` and
`proofInitial : ∀ A, IsInitial (proofs A)`.
Its `presentationGeneration` applies `generated` to
`imageSubobject A.hom`. It does not demand an initial derivation algebra for every morphism into S.

The principal declarations `extensive`, `monotone`, `idempotent`,
`generated_eq_pullback`, `adjunction`, `presentationHomEquiv`,
`presentationAdjunction` and `presentationGeneration_obj` cover the printed theorem. The checks quantify over the same subobject-indexed family.

The older `V46FirstOrderGeneration` and
`V46FirstOrderPresentationAdjunction` use the stronger assumption of initial derivation algebras for every axiom presentation. They remain auxiliary. The new principal reflector does not use their all-presentation assumption to prove 4.4. Their retained comparison lemmas explicitly state that stronger context. Calling the old construction alone a full proof of the printed theorem would be wrong; the current table no longer does so.

### 4.5: translations and Galois connections

`FirstOrderPresentation` also indexes proof algebras by axiom subobjects.
A `Translation` contains the three maps of terms, formulas and sentences,
constructor/substitution laws and an existential logical-axiom-instance map.
The existential witnesses are not additional data distinguished by equality of translations: `Translation.ext` depends only on the three maps.
The remaining rule maps are constructed from constructor preservation.

`Translation.map_generated_le` constructs a finite-proof translation.
`inverse_closed` derives inverse-image closure from this map.
`pushforward`, `inverseImage`, `adjunction`,
`generation_functor_identity`, `pushforward_comp` and
`inverseImage_comp` give the stated operations and equations.
`V46FirstOrderTranslationReflection` constructs the further reflection of axiom presentations into closed theories. No assumed closure-preservation field replaces the proof.

### 4.6: comparison and its hypotheses

`V46DeductionComparison` explicitly accepts the sentence-derivation maps
`proofMap` and their conclusion equations, exactly as the proposition does.
The code's regular-epimorphism preservation condition is no stronger than the printed regularity condition on G. The two generation squares are equalities of functors; `inclusionComparison` is a natural transformation; `right_closed` and `restrictedAdjunction` prove the restricted right adjoint.

`V46DeductionSliceAdjunction` implements the pullback right adjoint induced by an ambient adjunction.
`V46DeductionMates` constructs the right-adjoint inference algebra, its initial fold and the transposed sentence morphism from the printed rule natural transformation.
The code assumes that natural transformation in the illustrative construction, as does the manuscript. It does not simply assume the desired sentence map in that construction.

### 4.7–4.8: free signed theories

`NullaryPresentations` contains syntax for every coefficient object and derivation initiality for each sentence axiom subobject. It does not contain a universal interpretation as an unproved field.
`V46NullaryLogicalInterpretation` constructs the interpretation and logical-rule map.
`V46SignedFirstOrderCategories` defines disjoint consistent pairs and the category of consistent closed theories.
`V46SignedFirstOrderAdjunction` constructs the natural hom equivalence and the adjunction. Its unit is the atomic sentence map; its counit is sentence evaluation.
The extraction object's consistency is proved by evaluation into the given consistent theory.

`V46SignedSubobjectIncompleteness` defines essential incompleteness as base consistency plus incompleteness of every closed consistent extension.
Its forward direction uses the constructed Boolean complete extension;
its reverse direction uses the atomic reduction.
`V46SignedFirstOrderIncompleteness` obtains the restriction-category statement through `RestrictionSubobjects.inseparable_iff`.
The requisite subobject/domain comparison is a theorem using splittings and the printed monic partial inverses, rather than an assumed equivalence.
The explicit checks include both consistency and the disjoint-pair hypothesis.
No completed-row hypothesis discrepancy was found here.

### 5.1: actual slices and the full constant-object subcategory

`V46PartialSliceTuringTheoremChecks` checks Turing structure in the original restriction splitting and in `PartialMaps.Par (Over T)`.
It checks the actual full subcategory of objects `T × X → T` for original objects X, not merely an indexed substitute with no comparison.
`V46ConstantSliceFull` defines that full subcategory, proves agreement of its inherited and product-induced restriction, supplies its prodominical/isotype/Turing structure, and proves the exact object range of its realization.

Its completion equivalence targets the actual monic-span quotient.
Both directions preserve restriction.
The generic completion theorem requires total embeddings with partial retractions, which are subsequently supplied by the slice construction.
The code requires total pullbacks and monic partial inverses, supplied by the manuscript hypotheses. It does not assume the conclusion as an interface.

### 5.2: both adjunctions include the partial second unit

`V46TheoryExtensionsChecks` is detailed enough to distinguish the relevant functors from abstract functors having similarly named properties.
It checks that postcomposition maps `ofSpan s` to the same span under `Over.map i`; reindexing equals the functor induced by ordinary span pullback.

The checks exhibit both natural hom equivalences and both adjunctions.
The second unit is explicitly the partial inverse of the pullback inclusion, and is non-total at the terminal family for a proper inclusion.
Thus no total-unit assumption has silently strengthened the theorem.
Fullness, faithfulness, restriction preservation, failure of essential surjectivity, strict identity/composition, binary restriction-product comparison and both projection equations are present.

The printed sentence/theorem square is checked for literal total maps
`t, u, i` with `i ≫ u = t`.
The sentence-family isomorphism and the actual subobject inequality in the partial slice are checked separately.

### 5.3 and the application rows

`V46AssociatedEvaluation` constructs evaluation by ordinary pullback at the global logical theorem and gives the natural retraction.
`V46AssociatedBooleanDecision` proves:
(1) incompleteness iff the associated Boolean partial morphism is not total; and
(2) source inseparability iff that associated morphism has no total extension.
The source restriction-idempotent version is also present.
`V46AssociatedExtensionWitness` obtains no-total-extension from a total reduction of an inseparable pair for every consistent extension.

These results do not by themselves establish that every relevant transferred subobject is a closed sentence theory, or establish the full essential-incompleteness equivalence.
The current source table and latest verification report explicitly leave those obligations open.

For the application rows, existing modules were sampled to check that the table is distinguishing partial progress from completion.
`V46MillerDerivationTotal` constructs base-category arbitrary-rule initiality, while `V46MillerSyntaxUniformInitial` supplies parameterized syntax. These are not yet the every-parameter finite-derivation statement of 9.6.
`V46ForkDerivationInitial` and `V46ForkDerivationImages` concern the propositional fork rules and their generated image; they do not establish 10.7–10.8.
No current application row is incorrectly promoted to proved in the table.

## Reproducibility evidence

The repository records a full 1,708-command v57 verification at proof commit
`45a8a6d017850a3a68fcecd01ad82f5a1a83674a`.
The later records are explicitly incremental:

| Result | Tested proof commit | Commands | Status |
|---|---|---:|---|
| 4.8/full baseline | `45a8a6d...` | 1,708 | Full success recorded |
| 5.1 completion | `d2acc5c...` | 25 | Incremental success recorded |
| 5.2 completion | `f4572a0...` | 30 | Incremental success recorded |
| 5.3 subgoals | `f147a49...` | 22 | Incremental success recorded |

All three inspected incremental command arrays have the stated number of commands, zero exit codes throughout and SHA-256 log hashes. Their selected-axiom dictionaries have the stated 106/125/125 entries and use only `propext`, `Quot.sound` and `Classical.choice`.

The latest record reports 919 current production modules, 28,383 current declarations and 1,274 retained declarations. These are recorded transitive-audit counts, not counts independently reproduced by this review.

An independent comparison of the complete pinned Git trees establishes:
- Every Lean blob at current `dfe6d3b...` equals its blob at the latest tested proof `f147a49...`.
- `scripts/verify.py`, `SOURCE_PINS.json`, toolchain and dependency manifest also match that tested proof.
- Against the full baseline `45a8a6d...`, 63 Lean files are added. Five existing Lean files change: the main import root, both current audit files, `V46StatementAudit.lean` and `RestrictionSpanPullbacks.lean`. No preexisting V46 theorem implementation is changed in that comparison.

The recorded evidence therefore supports an unchanged tested Lean state at current HEAD, combined from the full baseline and later incremental verification. It does not support describing HEAD as having received a new 1,708-command full replay.

The toolchain is pinned to `leanprover/lean4:v4.35.0-rc2`.
The Lake manifest records 16 packages; the explicit mathlib and Foundation revisions match `lakefile.toml`.
`SOURCE_PINS.json` has 357 entries. The verifier intentionally omits the project-maintained `Lean/lakefile.toml`, leaving the reported 356 source comparisons. This is not an off-by-one discrepancy.

The apostrophe parser repair is present. Its independent raw-name accounting catches omitted, truncated and duplicate reports; unexpected axioms remain rejected. All six committed regression tests were run successfully here against the exact parser function extracted from the current source. This was a Python parser test, not a Lean proof replay.

The raw verification logs and complete measured-input snapshots referred to by the reports are under `.codex-work` and are not committed in the pinned tree. Their hashes and summary records are available; the raw bytes were not available for independent authentication in this review. The original 62-result coverage is supported by the retained mapping and recorded build history, but was not independently re-established theorem by theorem here.

## Verdict

The current table correctly separates seven completed additions from eight open obligations. The previous all-morphism/all-subobject discrepancy is repaired in the principal reflector. No further completed-row mismatch was found in the declarations and statement checks inspected.

A precise report of progress is: “69 of 77 numbered results have recorded verified Lean counterparts; 5.3 and seven application results remain open. Current Lean sources match the latest incrementally verified proof commit.” A claim that all fifteen additions are formalized, or that a new full kernel replay of current HEAD was performed in this review, would be false.

