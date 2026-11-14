# Manuscript v58: Lean impact review

The v58 changes require no change to the existing Lean theorem statements or proofs. The current abstract presentation interfaces already require initial derivation algebras only for axiom subobjects. The Boolean and quantifier corrections agree with the existing implementations. The composition statement is proved by an equivalent construction with different choices of program indices.

Reviewed source: `df66b19853e6b243170725619bfabb71f4741065` on `flengyel/CategoricalEssentialIncompleteness/main`, 14 November 2026.

## Comparison with the manuscript

| Manuscript point | Lean evidence | Effect |
| --- | --- | --- |
| Initial derivation algebras are required only for axiom subobjects. | `FirstOrderPresentation.proofs` and `.initial` in `V46LogicalTranslations.lean:34–41`; `NullaryPresentations` in `V46NullaryPresentationAdjunction.lean:27–31`. | The current principal interfaces already use the printed weaker hypothesis. |
| Generation from an arbitrary axiom morphism first takes its image. | `FirstOrderReflection.presentationGeneration` in `V46FirstOrderReflection.lean:155–157` generates `imageSubobject A.hom`. | No initial algebra for the arbitrary morphism is required. Older all-morphism interfaces are retained for explicitly stronger comparison results; the concrete syntactic instance constructs their initial algebras. |
| Corollary 4.8 interprets universal quantification by the second projection. | `NullaryBooleanValuation.algebra` uses `prod.snd`; `.quantifier_value` proves the constructor equation. Its statement check already asserts that equation. | No change. |
| Appendix B takes truth to be the second coproduct summand. | `Two.point true = coprod.inr`; `Fork.EqualityDecision` uses equality to `true`. | No change. |
| Lemma 6.1 has a uniform PA-provable composition equation for the same evaluator. | `UniformTrace.compose_eval`, `composition_PA`, `builders_totality_PA`, and `arithmetized_evaluation`, with existing statement checks. | No change to the lemma counterpart. The proof applies to arbitrary internal indices, not only standard natural-number indices. |
| The abstract states the essential-incompleteness equivalence of Theorem 5.3. | The retraction and the Boolean partial-morphism equivalences are proved; transfer of closed theories remains open. | The wording does not complete the missing Lean proof. |
| Reference correction and deletion of repeated prose. | No mathematical statement changes. | No Lean effect. |

All **77 numbered result statements and three numbered definition environments** are byte-identical between the reviewed v57 and v58 sources. This comparison concerns statement environments, not their proofs. The detailed [Boolean](lean-bool-impact.md), [composition](lean-composition-impact.md) and [axiom-subobject](lean-axiom-subobjects.md) reports accompany this review.

## Difference between the composition proofs

The revised paragraph chooses a composition program by specialization of a fixed sequential-simulation program. Lean chooses a fixed program for the functional relation defining composition and applies its parameter compiler. It proves the same uniform PA identity and primitive recursiveness of the resulting builder. The public specialization equation and the internal compiler use different parameter encodings.

No inspected Lean declaration identifies the already selected `compose` definition with the paragraph's literal expression `specialize(c, ExponentialPairing.code(f,e))`. Nor does this review claim that the paragraph's two trace transformations have been formalized as named functions. Those are details of an alternative proof, not additional conclusions in Lemma 6.1. The existing formalization supports the lemma statement; it does not reproduce that paragraph line by line.

## Verification evidence and its limits

The **2,377** current Lean and verification-input Git blobs compared with proof commit `f147a49ecddc87509b02156a912b0b0dbbdbce68` are identical. This covers every file under `Lean/`, including toolchain and dependency manifests, plus `SOURCE_PINS.json`, `LOCAL_PATCHES.json`, `scripts/verify.py`, `scripts/check_manuscript.py`, and `scripts/verify-wsl.sh`. No Lean file was removed. The comparison is recorded in `lean-input-comparison.json` and is reproducible from the two Git trees.

The committed record `docs/V57_ASSOCIATED_RETRACTION_VERIFICATION_2026-11-14.json` reports a successful incremental verification of that proof commit: 22 commands, project and statement-entry builds, selected strict elaborations, and both complete transitive axiom audits. It reports 919 current production modules, 28,383 current declarations and 1,274 retained declarations, with axiom union `propext`, `Quot.sound`, `Classical.choice`. The record expressly says that unchanged production files were not all individually re-elaborated. Its preceding full and incremental verification records remain the supporting baseline.

This review inspected declarations, their proofs and statement checks, and compared committed source hashes. **It did not run a fresh Lean build or kernel audit:** neither `lean` nor `lake` is installed in this review environment. Equality of the committed inputs preserves the applicability of the recorded source-level evidence; it is not a new execution of those checks.

## Remaining formalization work

The recorded status remains **69 of 77 numbered results proved**, with eight open: **5.3, 8.9, 8.10, 9.6, 9.8, 10.7, 10.8 and 10.9**. Theorem 5.3 still requires transfer of closed sentence theories, preservation of consistency and completeness for those theories, and the full essential-incompleteness equivalence and extension conclusion. The v58 revisions neither remove nor add those obligations.

No Lean source or proof-status entry was changed by this review.
