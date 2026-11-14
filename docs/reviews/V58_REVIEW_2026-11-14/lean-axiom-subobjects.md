# Axiom subobjects and arbitrary axiom morphisms in the current Lean sources

Pinned repository commit: `df66b19853e6b243170725619bfabb71f4741065`. Seventeen additional source files were fetched at that commit and their blob SHAs checked against its recursive tree and the local Git blob hashes. The exact sources are listed in `lean-axiom-source-manifest.json` and are retrievable at the pinned commit.

## Conclusion

The principal general constructions require initial derivation algebras **only for axiom subobjects**. They define generation of an arbitrary axiom morphism `a:A→S` by first taking its regular image, `Gen(im a)`. They do not infer that an initial derivation algebra for `a` itself exists.

Older APIs requiring initial algebras for all axiom morphisms remain in the source. Their stronger hypothesis is explicit. They are used in a comparison section under that hypothesis and in a concrete arithmetic realization where it is proved. They are not the hypothesis of `FirstOrderPresentation`, `NullaryPresentations`, or the principal reflector and translation theorems. No unresolved mismatch of these two assumptions was found in the inspected interfaces.

## Exact general definitions

| Declaration | Source and lines | Quantification |
|---|---|---|
| `CategoricalEssentialIncompleteness.V46.FirstOrderReflection` parameter `proofs` and `proofInitial` | `V46FirstOrderReflection.lean:33–35` | `A : Subobject S`, followed by `IsInitial (proofs A)` for each such A. |
| `FirstOrderReflection.presentationGeneration` | `V46FirstOrderReflection.lean:155–158` | An arbitrary `A : Over S` is sent to `generated proofs (imageSubobject A.hom)`. No proof algebra for `A.hom` is used. |
| `FirstOrderReflection.presentationAdjunction` | `V46FirstOrderReflection.lean:182–187` | The arbitrary-presentation reflection is built from the subobject initiality parameters above. |
| `CategoricalEssentialIncompleteness.V46.FirstOrderPresentation` | `V46LogicalTranslations.lean:34–41` | `proofs` takes an axiom `Subobject syntaxData.sentenceObject`; `initial` quantifies over those subobjects. |
| `CategoricalEssentialIncompleteness.V46.NullaryPresentations` | `V46NullaryPresentationAdjunction.lean:27–31` | For each label object X, proofs and initiality are required for axiom subobjects of its sentence object. |
| `NullaryInterpretation.presentation` | `V46NullaryLogicalInterpretation.lean:61–71` | Packages only the subobject-indexed proof family into `FirstOrderPresentation`. |
| `FirstOrderPresentation.Axioms` | `V46FirstOrderTranslationReflection.lean:33–35` | Stores a first-order presentation and an axiom subobject. Its generation functor at lines 99–107 uses the subobject reflector. |
| `DeductionComparison` parameters `proofMap` and `proofConclusion` | `V46DeductionComparison.lean:86–94` | Compare derivations for `A : Subobject ...` and the regular image of its interpreted inclusion. |

The existing independent statement checks retain this scope. `V46FirstOrderReflectionChecks.lean:26–28` introduces only the subobject family; lines 50–61 check the image-generation equation, hom-set equivalence, and arbitrary-presentation adjunction under that family.

## Where the stronger hypothesis remains

`V46FirstOrderGeneration.lean:36–39` and `V46FirstOrderPresentationAdjunction.lean:35–37` take an algebra and its initiality for every `a:A→S`, without requiring `a` to be monic. Those signatures are stronger than the manuscript's general subobject existence assumption.

In `V46FirstOrderReflection.lean:189–193`, the section `PresentationComparison` explicitly reintroduces that stronger family. Its `presentation_generated_comparison` at lines 214–229 proves that the generated image obtained from direct derivations for `a` equals generation from `im a`. The result assumes both relevant initial constructions through the stronger family. It does **not** construct initiality for an arbitrary `a` from initiality for its image.

The concrete arithmetic use discharges the stronger assumption. `V46SyntacticGeneratedTheoryTotal.proofAlgebra` and `.proofInitial`, at `V46SyntacticGeneratedTheoryTotal.lean:34–40`, construct the actual algebra and its initiality for any `axioms:A→S`, using `SyntacticDerivation.totalDerivationInitial`. They have no extra initiality argument supplied by the caller. `V46SyntacticGenerationAdjunction.lean:95–104` constructs the manuscript reflector through `im a`; lines 106–109 then identify it with the direct concrete axiom-morphism construction, using the already proved `proofInitial`.

The underlying syntactic finite-rule construction is also not restricted to monic nullary rules: `V46SyntacticDerivationInitial.lean:24–25` takes an arbitrary `RulePresentation F N`, and `.derivationInitial` is constructed at lines 62–64. Similarly, `V46MillerDerivationInitial.lean:28` takes arbitrary finite rule data in the total uniform category and constructs `.derivationInitial` at lines 48–51. These concrete results are stronger constructions, rather than hidden general assumptions.

## Consequences for the claimed results and status

The current forms of Theorems 4.4–4.8 can use `FirstOrderReflection`, `FirstOrderPresentation`, and `NullaryPresentations` at the printed subobject hypotheses. The arbitrary axiom-morphism input to the reflector is handled by regular image factorization. The concrete arithmetic comparison may additionally use the stronger direct-derivation implementation because that existence result is constructed in its category.

The status file explicitly records the distinction at the retained `FORMALIZATION_STATUS_V57.md` and the current `FORMALIZATION_STATUS_V58.md`: only subobject initiality is required by the current reflector, while the older all-morphism implementation is retained under its stronger stated assumption and compared only at the level of generated sentence images. The rows for 4.4 and 4.5 also state the subobject scope. Thus the distinction is documented rather than silently treated as an equivalence of initiality hypotheses.

This targeted check does not discharge the eight separately tracked mathematical obligations. In particular, the parameterized Miller deduction result 9.6 and first-order fork results 10.7–10.9 still require their concrete realization work; the general subobject API does not supply it automatically. The status table labels these open. Their existence requirements should remain explicit when the general results are instantiated.

No Lean edit is indicated by this particular issue. This is a source-level signature and use audit, not a new kernel replay or a full proof of every imported initiality theorem.
