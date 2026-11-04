# V46 next proofs and correspondence — 4 November 2026

This batch proves general primitive-recursive tag representation, categorical
deletion and free-variable equations, identity substitution, quantified
admissibility, partial search with its even/odd model comparison, arbitrary
c.e. propositional Hilbert axiom closure, numerical tuple and monic-span
comparisons, and theory-family coherence. It constructs list folds and
initiality in every parameter slice of both the predicate category and the
total-split category, completing Proposition 5.6 in the production
presentation. The full v46 formalization remains open.

The current [correspondence table](../FORMALIZATION_STATUS_V46.md) covers
all 62 numbered results, three definitions and the required unnumbered
constructions. Earlier implementation and verification reports are
preserved. The manuscript entry point remains `manuscript/latex/main.tex`;
no manuscript source, PDF or archive is changed.

## Source and correspondence

Work continued in the existing WSL2 checkout on `main`, starting at
`ccd24e2073e6702638e804044088ab8865fc85c6`. A fetch found no incoming
changes at the start. All 345 verification-input hashes matched the prior
successful final verification, whose source identity was
`938d13139abe663c2d57d39a4de2700cc34cedf629f888019383a27e13c258c3`.
That successful baseline was reused before implementation. All prior proof
modules and their declaration coverage are retained. Only the combined
entry point and v46 statement-audit imports change among previous verifier
inputs; the remaining additions are new proof and check modules.

The checked principal signatures of 5.3, 6.4, 6.8, A.3 and A.6 retain their
reported hypotheses. Two stale status entries were corrected: generic
admissible substitution was still described as pending under A.1, and an
unnumbered row still described the predicate equivalence as pending.

There is a substantive, already-recorded presentation gap. Section 5 uses
exponential product pairing and even/odd coproduct codes. Production Lean
uses square pairing, pair-tagged coproduct membership subsets, and a stage
graph at each standard program index. The new parity comparison proves the
even/odd coproduct graph and its inverse on whole PA models. The exponential
product and printed uniform trace comparisons remain pending under 5.1.
Consequently, results stated below in the production presentation are not
reported as a completed identification of the two presentations.

## Proved results

Here `V46` abbreviates `CategoricalEssentialIncompleteness.V46`. Lean
composes source morphisms left to right with `≫`.

| Manuscript result or construction | Declarations and effective hypotheses |
| --- | --- |
| Lemma 5.4 | `PrimitiveRecursiveTags.natPrimrec_representation`, `primrec_representation`, `Code.graph_existsUnique`, `graph_total_PA`, `graph_pi_total_PA`, `graph_coherent_PA`, `selected_membership_PA`, `selectedList_eval`. Structural primitive-recursion codes produce actual Σ₁ and Π₁ graphs, PA-provable unique totality and coherence, and standard interpretation equal to the supplied reader. The recursion step constructs a Foundation `PR.Construction`; its totality includes nonstandard indices. Finite tagged membership uses this constructed interpretation and requires valid finite tags. It does not identify arbitrary standard-extensionally-equal programs in PA. |
| Appendix A.2 deletion | `StableListAlgebra.membership_deletion_parameter`, `membership_deletion`. For arbitrary regular finitary extensive D and internal decidable equality on V, parameterized initiality proves `mem(x,del(y,w)) = ¬ε(x,y) ∧ mem(x,w)` as a morphism equation. The proof uses actual internal truth fibers, not global-point induction. |
| Appendix A.2 free variables | `CategoricalSyntax.variable_occurrences`, `function_occurrences`, `equality_occurrences`, `relation_occurrences`, `implication_occurrences`, `quantifier_occurrences`, `variable_membership`, `quantifier_membership`, `quantifier_bound_name_absent`. These are the actual simultaneous occurrence fold's constructor equations, with arbitrary coefficients and named variables under Definition A.1's initiality hypotheses. Negation preservation was already proved. |
| Appendix A.3 parameter change | `CategoricalSyntax.crossParameterFold`, `crossParameterFold_unique`, `fold_parameter_change`; `SyntaxParameterChange.reindexAlgebra`. For every `r:P→Q` and every target algebra over Q, postcomposition, its product comparison and preserved coproducts construct the heterogeneous polynomial map. Its adjunction mate gives the actual reindexed algebra and fold comparison. No inverse or section of r is assumed. |
| Appendix A.3 identity substitution | `CategoricalSyntax.term_substitution_identity`, `formula_substitution_identity`, `identityFormulaAdmissible`, `identityFormulaAdmissible_substitution`. The actual inputs `e_T` and `e_F` substitute `η(x)` for x. Terms are fixed; formulas return `ok` of the original formula and factor through the actual admissibility pullback. Quantifier cases retain named variables and the original-body equal-name branch. |
| Appendix A.3 quantified admissibility | `CategoricalSyntax.quantified_substitution_equation`, `quantified_admissibility_subobjects`, `quantified_admissibility_coproduct`, `quantifiedDistinctBody_square`, `quantifiedEqualAdmissible_result`, `quantifiedDistinctAdmissible_result`. Under the existing arbitrary-category syntax hypotheses, the actual quantified-input pullback of Adm equals the equal-name fiber joined with the distinct-name, capture and recursive-body success intersection. The disjoint summands form an actual monic coproduct. Both have actual Adm lifts and the displayed result equations; the distinct branch uses a constructed body-to-Adm pullback map. |
| Partial search underlying Lemma 7.2 | `PartialSearchLift.lift`, `partial_lift`, `mem_model_lift`, `model_lift_domain`, `pull_summand0`, `pull_summand1`, `lift_comparison`. For any two unary Σ₁ predicates, the source arrow is chosen before the model and disjointness proof. Its exact partial graph and reversed fibers hold in every PA model where the predicates are disjoint. Neither coverage nor PA-provable disjointness is required. The actual categorical Γ-provability instance remains open. |
| Even/odd comparison | `PartialSearchLift.mem_parity_encode_inl`, `mem_parity_encode_inr`, `mem_parity_decode_inl`, `mem_parity_decode_inr`, `parityLift_decode`, `mem_parityLift`. Existing PA-verified source indices give the actual model sum-to-number isomorphism. In every PA model where the predicates are disjoint, the whole partial graph is positive evidence at `2x+1` and negative evidence at `2x`; decoding recovers the original source arrow. |
| Fixed syntactic diagonal comparison | `PartialSearchLift.syntactic_partial_comparison`, `syntactic_predicates_noncoverage`. The actual partial lift and the fixed syntactic Turing morphism instantiate Theorem 3.1. Model-disjoint Σ₁ predicates bounding the mapped diagonal idempotents have a total source witness with both inverse images zero and an element outside their union. Concrete Γ syntax, theorem-idempotent bounds and standard soundness remain separate. |
| General c.e. axiom closure | `ForkAxiomClosure.derives_iff_record`, `derives_least`, `derives_re`, `theoremCodes_re`, `endpoint_axiom_extension_incomplete`. Arbitrary c.e. axiom-code sets generate an actual propositional Hilbert consequence relation. A proved finite-record comparison and supported-leaf search make the theorem set c.e. Consistency and extension of either actual coded endpoint yield an independent formula, with no compatible-family assumption on the extension. This does not construct the H-initial proof object of 9.3. |
| Appendix D coherence | `SyntacticFamilyCoherence.quotient_id`, `quotient_comp`, `modelIndex_id`, `modelIndex_comp`, `projection_id`, `projection_comp`, `square`, `square_comp_coherence`, `square_unit_coherence`. These use the actual quotient functors and full arithmetic-model index restrictions. Pasted and direct squares agree as natural isomorphisms, including associators and whiskers. Consistency and c.e. hypotheses are unnecessary; the composite inclusion is derived. |
| Proposition 7.7 | `NumericalTuples.equivalence`, `classicalTotalEquivalence`, `tupleRegular`, `tupleFinitaryExtensive`, `monoInverse`, `mappedMono_partialMono`, `partialMapEquivalence`, `partialMap_preserves_restrictions`, `inverse_preserves_restrictions`, `partialMap_preserves_ranges`. Literal dimensions carry c.e. subsets of finite numerical tuples. Morphisms are functions with partial-recursive tuple realizers, equal by function equality. Dimension zero is Unit with proper code image `{0}`; dimension one is N with identity coding. Guarded decoding proves graph/domain/function comparisons and the total-category equivalence. Mono inverses and ordinary monic-span equivalence use the verified numerical-carrier choice instance, followed by its splitting equivalence; no global choice instance on `Split(Rec)` is assumed. |
| Proposition B.2 | `NumericalTuples.forkEquivalence` composes the actual total-fork equivalence with the tuple-category equivalence on diagrams of shape `WalkingSpan`. Explicit checks retain finite limits/coproducts of both categories, regularity/extensivity of the fork category, `EffectiveFork.total_mono_iff_injective` and `imageIsImage`. The existing range subfunctor supplies the actual component image factorization. |
| Initial-algebra transport | `AlgebraTransport.equivalence`, `initial`, `initialIff`. For arbitrary base-category equivalence E and natural comparison `F⋙E≅E⋙G`, a constructed full, faithful, essentially-surjective algebra functor gives an actual equivalence of algebra categories and transports initiality. No regularity or finiteness assumption is imposed on this generic result. |
| Monic-span comparison | `PartialMapEquivalence.equivalence`, `preserves_restrictions`, `inverse_preserves_restrictions`, `preserves_ranges`. For `E:D≌Tot(R)`, D and Tot(R) with pullbacks, and split R with ranges and weak choice, mapping actual monic spans through E constructs `Par(D,Mono)≌R`. Pullback composition, reflected apex isomorphisms and counit-transferred inverse spans prove the functor laws and equivalence. Both directions preserve restrictions; the forward functor preserves ranges when the source has ranges, in particular for regular D. The numerical application uses the verified numerical-carrier choice instance. |

Concrete list results use the actual category of Σ₁ predicates and
T-provably supported uniquely-total graphs, modulo T-provable equality,
under only `T≥PA`. `SyntacticListEvaluation.SliceAlgebra.evaluationMorphism`
constructs finite value records, with internal existence/uniqueness at all
model lengths. `evaluation_nil_equation`, `evaluation_cons_equation` and
`evaluation_unique` give the graph universal property.
`SyntacticLists.decode`, `fold`, `fold_nil`, `fold_cons`, `fold_unique` and
`withParametersInitial` turn every actual algebra in `Over P` into that
graph presentation and prove its unique categorical algebra morphism.
`stableListAlgebra` constructs base and every-parameter initiality;
`Transport.mappedStableListAlgebra` proves the actual slice and constructor
comparisons through an arbitrary equivalence. Its application
`totalStableListAlgebra T V` supplies the full bundle for every object V
of `Tot(Split(S_T))`, completing Proposition 5.6 under only `T≥PA`.
Auxiliary set interpretations provide finite geometry and faithfulness;
the proof does not assert that nonstandard internal lists are initial among
all set functions.

## Verification and review

All Lean/Lake jobs were serialized with `.codex-work/build.lock` and
`LEAN_NUM_THREADS=1`. Targeted production builds and explicit statement
modules were replayed with `lake env lean -DwarningAsError=true`.
Original failed replays and recorded input hashes remain in ignored run
directories; agent run directories also retain their source copies. Completed
sources are checked again by the full verifier. The final small fork wrapper
first failed because `WalkingSpan` required the `CategoryTheory.Limits`
namespace; the corrected build and strict replays passed at
`.codex-work/v46-next-root/20261104T110803485647Z`. Its failed predecessor
`20261104T110733965198Z` is retained. No mathematical hypothesis changed.

The pinned environment is unchanged: Lean `v4.35.0-rc2`, compiler
`11acb17ec6b07a8f9e9173e6845197929540936b`; Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; Foundation
`01f617fbe240a84aaf1c45b31b9d65e0a2e21c1d`. The existing verifier retains
the v5 audit, manuscript and imported-source pins, dependency checks and
the complete v46 transitive axiom inspection.

Independent agents reviewed the changed statements, concrete constructions
and correspondence. No new whole-paper correctness, independent-kernel or
registry verification claim is made. Mathematical-writing review is
restricted to the revised correspondence and implementation notes; the
official Knuth–Larrabee–Roberts source was consulted.

## Final verification and committed source

`bash scripts/verify-wsl.sh` ran the existing
`LEAN_NUM_THREADS=1 python3 scripts/verify.py` and exited **0**. All
151 recorded commands passed: combined build, v5/v46 statement
audits, every strict v46 module replay, source/manuscript/dependency pins,
and transitive axiom inspection. The final run is
`.codex-work/verify-20261104T110830Z-R1pFJ0`. It verified
356 imported-source pins, 24 v46 manuscript files and
16 dependency revisions. All 1274 retained declarations and
3044 declarations from 79 v46 production modules were audited;
the axiom union is exactly `Classical.choice`, `Quot.sound` and `propext`.
Every previously audited declaration is retained.

The tested source identity is
`24fb391673b0ddb55f0c8039894227857e8fa95ab9ff0c0a4a85125781b49801`.
All 404 verifier-input hashes were compared with `git show` bytes at
proof commit `4b54dd15bd6b871d7211b749db259a16bae7055c` and match. This batch adds 59 Lean files;
343 previous inputs are unchanged and the two changed previous inputs add
imports. No source changed during the successful full verification.

The proof commit was pushed normally to `origin/main`; the push exited 0
and the remote ref was checked at that exact commit. The accompanying
report commit changes documentation only. Its final synchronized commit
and the delivered-byte hashes are recorded in `DELIVERY_SHA256.json`
alongside the Downloads copies. The active Windows profile and Downloads
known folder were queried directly; the existing destination is
`C:\Users\fleng\Downloads` (`/mnt/c/Users/fleng/Downloads`).

The [verification record](V46_NEXT_PROOFS_VERIFICATION_2026-11-04.json)
contains command arguments, exit codes, pins, input hashes and both axiom
audits. The [changed-source manifest](reviews/V46_NEXT_PROOFS_SOURCE_SHA256_2026-11-04.txt),
[author-side mathematical review](reviews/V46_NEXT_PROOFS_REVIEW_2026-11-04.md)
and [writing review](reviews/V46_NEXT_PROOFS_WRITING_2026-11-04.md) state the
checked scope and remaining qualifications.

## Remaining obligations

The first large concrete syntax dependency remains 5.5: named two-sort
syntax and its parameter-slice evaluation/initiality for arbitrary
coefficients. The generic absent-variable substitution equations also remain open.
The inference realization of 5.8 and the named syntax,
substitution and Craig/LK comparisons are also required. Standard decoded
semantic substitution and soundness, the actual Γ-provability comparison
and categorical arithmetic chain, indexed theories and uniform independent
sentences, representation-independent Miller realizations, and cosheaf
H-initial proof presentation remain open. The correspondence table records
their exact scope separately from the proved generic constructions.
