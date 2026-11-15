/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticSignedConsistency
public import CategoricalEssentialIncompleteness.V46SubobjectImagePresentations
public import CategoricalEssentialIncompleteness.V46SignedFirstOrderGeneration

/-! # Regular-image generation of the arithmetic diagonal signed theory -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ArithmeticSignedAtoms
instance numberInclusion_mono (C : PredicateCategory 𝗣𝗔) : Mono (numberInclusion C) := by
  dsimp only [numberInclusion]
  infer_instance

local notation "N" => (PrintedObjectCoding.Number : PredicateCategory 𝗣𝗔)
def positiveSubobject : Subobject (C := PredicateCategory 𝗣𝗔) N :=
  Subobject.mk (numberInclusion ArithmeticDiagonalCodes.alpha)
def negativeSubobject : Subobject (C := PredicateCategory 𝗣𝗔) N :=
  Subobject.mk (numberInclusion ArithmeticDiagonalCodes.beta)
end CategoricalEssentialIncompleteness.V46.ArithmeticSignedAtoms

namespace CategoricalEssentialIncompleteness.V46.ArithmeticSignedTheoryTruth
open SyntacticDerivation ArithmeticSignedAtoms
local notation "N" => (PrintedObjectCoding.Number : PredicateCategory 𝗣𝗔)
variable {V : PredicateCategory 𝗣𝗔}
variable (S : CategoricalSyntax V (fun _ => ⊥_ (PredicateCategory 𝗣𝗔)) (fun _ => N) 0)

/-- Initial derivation algebras are indexed by axiom subobjects. -/
def proofFamily (A : Subobject S.sentenceObject) :
    Endofunctor.Algebra (S.logicalRules A.arrow).inference :=
  derivationAlgebra 𝗣𝗔 (S.logicalRules A.arrow)

def proofFamily_initial (A : Subobject S.sentenceObject) : IsInitial (proofFamily S A) :=
  derivationInitial 𝗣𝗔 (S.logicalRules A.arrow)

/-- An arbitrary axiom morphism generates through its regular image.
The source code algebra is the constructed arithmetic derivation algebra. -/
theorem presentation_image_comparison {A : PredicateCategory 𝗣𝗔} (a : A ⟶ S.sentenceObject) :
    imageSubobject (pullback.snd (derivationAlgebra 𝗣𝗔 (S.logicalRules a)).a.hom S.sentenceInclusion) =
      FirstOrderReflection.generated (proofFamily S) (imageSubobject a) := by
  let I := imageSubobject a
  let e := factorThruImageSubobject a
  let : IsSplitEpi (factorThruImage a) := PredicateModelSubobjects.factorThruImage_isSplitEpi 𝗣𝗔 a
  let : IsSplitEpi e := by
    dsimp only [e, factorThruImageSubobject]
    infer_instance
  have he : e ≫ I.arrow = a := imageSubobject_arrow_comp a
  have hs : section_ e ≫ a = I.arrow := by
    calc
      _ = section_ e ≫ (e ≫ I.arrow) := congrArg (fun f => section_ e ≫ f) he.symm
      _ = (section_ e ≫ e) ≫ I.arrow := (Category.assoc _ _ _).symm
      _ = I.arrow := by rw [IsSplitEpi.id, Category.id_comp]
  apply le_antisymm
  · exact firstOrder_sentence_image_monotone S.logicalAxioms S.sentenceInclusion a I.arrow
      S.quantifierConstructor S.implicationConstructor e he
      (derivationAlgebra 𝗣𝗔 (S.logicalRules a)) (derivationInitial 𝗣𝗔 (S.logicalRules a))
      (proofFamily S I)
  · exact firstOrder_sentence_image_monotone S.logicalAxioms S.sentenceInclusion I.arrow a
      S.quantifierConstructor S.implicationConstructor (section_ e) hs
      (proofFamily S I) (proofFamily_initial S I) (derivationAlgebra 𝗣𝗔 (S.logicalRules a))

/-- All initial choices for an axiom subobject have the same generated
sentence image. -/
theorem generated_eq_canonical
    (proofs : (A : Subobject S.sentenceObject) →
      Endofunctor.Algebra (S.logicalRules A.arrow).inference)
    (initial : ∀ A, IsInitial (proofs A)) (A : Subobject S.sentenceObject) :
    FirstOrderReflection.generated proofs A =
      FirstOrderReflection.generated (proofFamily S) A := by
  apply le_antisymm
  · exact firstOrder_sentence_image_monotone S.logicalAxioms S.sentenceInclusion A.arrow A.arrow
      S.quantifierConstructor S.implicationConstructor (𝟙 _) (Category.id_comp _)
      (proofs A) (initial A) (proofFamily S A)
  · exact firstOrder_sentence_image_monotone S.logicalAxioms S.sentenceInclusion A.arrow A.arrow
      S.quantifierConstructor S.implicationConstructor (𝟙 _) (Category.id_comp _)
      (proofFamily S A) (proofFamily_initial S A) (proofs A)

/-- The signed axiom morphism presents the printed join of atomic images. -/
theorem signed_axiom_image :
    imageSubobject (axioms S) =
      (Subobject.«exists» (NullaryInterpretation.atomSentence S)).obj positiveSubobject ⊔
      (Subobject.«exists» (NullaryInterpretation.atomSentence S ≫ S.sentenceNegation)).obj
        negativeSubobject := by
  rw [positiveSubobject, negativeSubobject, SubobjectImagePresentations.exists_mk,
    SubobjectImagePresentations.exists_mk]
  exact PresentationLemmas.image_copair _ _

/-- The generated signed theory agrees with the original sentence image,
for every subobject-indexed choice of initial derivation algebras. -/
theorem signed_theory_eq (F : NullaryPresentations V) :
    (SignedFirstOrder.theory F positiveSubobject negativeSubobject).val =
      sentenceTheory (F.syntaxData N) := by
  change FirstOrderReflection.generated (F.proofs N)
    (SignedFirstOrder.axioms F positiveSubobject negativeSubobject) = _
  have ha : SignedFirstOrder.axioms F positiveSubobject negativeSubobject =
      imageSubobject (axioms (F.syntaxData N)) := (signed_axiom_image (F.syntaxData N)).symm
  rw [ha, generated_eq_canonical (F.syntaxData N) (F.proofs N) (F.initial N)]
  exact (presentation_image_comparison (F.syntaxData N) (axioms (F.syntaxData N))).symm

/-- Internal consistency holds for the actual generated signed theory. -/
theorem signed_theory_consistent (F : NullaryPresentations V) :
    (F.presentation N).Consistent
      (SignedFirstOrder.theory F positiveSubobject negativeSubobject).val := by
  change (SignedFirstOrder.theory F positiveSubobject negativeSubobject).val ⊓
    (Subobject.pullback (F.syntaxData N).sentenceNegation).obj
      (SignedFirstOrder.theory F positiveSubobject negativeSubobject).val = ⊥
  rw [signed_theory_eq]
  exact sentence_consistent (F.syntaxData N)

end CategoricalEssentialIncompleteness.V46.ArithmeticSignedTheoryTruth
