/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalArithmeticProofWords
import CategoricalEssentialIncompleteness.V46NumericalArithmeticGeometry
import CategoricalEssentialIncompleteness.V46SyntacticPredicatesRegular
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-! # The fixed provability predicate is the image of the literal proof-word conclusion -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.ProofImage
open NumericalCoordinates

abbrev provability (Γ : Carrier) : Carrier := ArithmeticLiteralModel.theoremPredicate Γ

private theorem provability_sentence (Γ : Carrier) :
    𝗣𝗔 ⊢ inclusionSentence (provability Γ) ProofWords.sentences := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff,inclusionSentence_eval]
  intro z hz
  obtain ⟨p,hp⟩ := (imageCarrier_eval (ProofWords.conclusion Γ).graph z).mp
    ((ProofWords.fixed_provability M Γ z).mpr hz)
  exact ((ProofWords.conclusion Γ).support_model M p z hp).2

/-- This is the same fixed Gamma predicate and the literal inclusion of
its sentence codes. -/
def sourceInclusion (Γ : Carrier) : GraphMorphism 𝗣𝗔 (provability Γ) ProofWords.sentences :=
  GraphMorphism.inclusion (provability_sentence Γ)

instance sourceInclusion_mono (Γ : Carrier) : Mono (representedArrow 𝗣𝗔 (sourceInclusion Γ)) :=
  SyntacticPredicates.inclusion_mono (provability_sentence Γ)

/-- The graph computes the original conclusion; its image membership is
proved rather than supplied as a field. -/
def sourceQuotient (Γ : Carrier) : GraphMorphism 𝗣𝗔 (ProofWords.carrier Γ) (provability Γ) where
  graph := (ProofWords.conclusion Γ).graph
  support := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    rw [models_iff,supportSentence_eval]
    intro p z hpz
    exact ⟨((ProofWords.conclusion Γ).support_model M p z hpz).1,
      (ProofWords.fixed_provability M Γ z).mp ((imageCarrier_eval _ _).mpr ⟨p,hpz⟩)⟩
  total := (ProofWords.conclusion Γ).total

theorem sourceQuotient_surjective (Γ : Carrier) :
    𝗣𝗔 ⊢ surjectiveSentence (provability Γ) (sourceQuotient Γ).graph := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff,surjectiveSentence_eval]
  intro z hz
  exact (imageCarrier_eval (ProofWords.conclusion Γ).graph z).mp
    ((ProofWords.fixed_provability M Γ z).mpr hz)

instance sourceQuotient_splitEpi (Γ : Carrier) :
    IsSplitEpi (representedArrow 𝗣𝗔 (sourceQuotient Γ)) :=
  (sourceQuotient Γ).isSplitEpi_of_surjective (sourceQuotient_surjective Γ)

theorem source_factor (Γ : Carrier) :
    representedArrow 𝗣𝗔 (sourceQuotient Γ) ≫ representedArrow 𝗣𝗔 (sourceInclusion Γ) =
      representedArrow 𝗣𝗔 (ProofWords.conclusion Γ) := by
  apply Quotient.sound
  apply complete.{0} 𝗣𝗔
  intro M _ _
  let _ : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  rw [models_iff,uniformSentence_eval]
  intro p z
  change (comp (GraphMorphism.identityGraph (provability Γ)) (ProofWords.conclusion Γ).graph).val.Evalb ![p,z] ↔
    (ProofWords.conclusion Γ).graph.val.Evalb ![p,z]
  rw [comp_eval]
  constructor
  · rintro ⟨y,hpy,hyz⟩
    obtain ⟨_,rfl⟩ := (GraphMorphism.identityGraph_eval (provability Γ) y z).mp hyz
    exact hpy
  · intro hpz
    exact ⟨z,hpz,(GraphMorphism.identityGraph_eval (provability Γ) z z).mpr
      ⟨((sourceQuotient Γ).support_model M p z hpz).2,rfl⟩⟩

def proofObject (Γ : Carrier) : NumericalTuples.Object := numericalInterpretation.obj (ProofWords.carrier Γ)
def sentenceObject : NumericalTuples.Object := numericalInterpretation.obj ProofWords.sentences
def theoryObject (Γ : Carrier) : NumericalTuples.Object := numericalInterpretation.obj (provability Γ)

def conclusion (Γ : Carrier) : proofObject Γ ⟶ sentenceObject :=
  numericalInterpretation.map (representedArrow 𝗣𝗔 (ProofWords.conclusion Γ))

def quotient (Γ : Carrier) : proofObject Γ ⟶ theoryObject Γ :=
  numericalInterpretation.map (representedArrow 𝗣𝗔 (sourceQuotient Γ))

def inclusion (Γ : Carrier) : theoryObject Γ ⟶ sentenceObject :=
  numericalInterpretation.map (representedArrow 𝗣𝗔 (sourceInclusion Γ))

instance inclusion_mono (Γ : Carrier) : Mono (inclusion Γ) := by
  dsimp only [inclusion]
  infer_instance

instance quotient_splitEpi (Γ : Carrier) : IsSplitEpi (quotient Γ) := by
  dsimp only [quotient]
  infer_instance

theorem factor (Γ : Carrier) : quotient Γ ≫ inclusion Γ = conclusion Γ := by
  exact (CategoryTheory.Functor.map_comp numericalInterpretation
    (representedArrow 𝗣𝗔 (sourceQuotient Γ))
    (representedArrow 𝗣𝗔 (sourceInclusion Γ))).symm.trans
      (congrArg numericalInterpretation.map (source_factor Γ))

private def mappedImage {C I D : PredicateCategory 𝗣𝗔}
    (q : C ⟶ I) (m : I ⟶ D) (f : C ⟶ D) (h : q ≫ m = f)
    [IsSplitEpi q] [Mono m] : StrongEpiMonoFactorisation (numericalInterpretation.map f) where
  I := numericalInterpretation.obj I
  m := numericalInterpretation.map m
  e := numericalInterpretation.map q
  fac := (CategoryTheory.Functor.map_comp numericalInterpretation q m).symm.trans
    (congrArg numericalInterpretation.map h)

/-- The fixed predicate supplies the concrete categorical image. -/
def imageFactorisation (Γ : Carrier) : StrongEpiMonoFactorisation (conclusion Γ) :=
  mappedImage (representedArrow 𝗣𝗔 (sourceQuotient Γ))
    (representedArrow 𝗣𝗔 (sourceInclusion Γ))
    (representedArrow 𝗣𝗔 (ProofWords.conclusion Γ)) (source_factor Γ)

def isImage (Γ : Carrier) : IsImage (imageFactorisation Γ).toMonoFactorisation :=
  (imageFactorisation Γ).toMonoIsImage

theorem conclusion_value (Γ : Carrier) (p : NumericalTuples.Point (proofObject Γ)) :
    (conclusion Γ).toFun p =
      (PredicateInterpretation.functor 𝗣𝗔 ℕ).map (representedArrow 𝗣𝗔 (ProofWords.conclusion Γ)) p := by
  exact numericalInterpretation_value (representedArrow 𝗣𝗔 (ProofWords.conclusion Γ)) p

@[simp] theorem inclusion_value (Γ : Carrier) (s : NumericalTuples.Point (theoryObject Γ)) :
    ((inclusion Γ).toFun s).val = s.val := by
  rw [inclusion,numericalInterpretation_value]
  have h := PredicateInterpretation.value_graph 𝗣𝗔 ℕ (sourceInclusion Γ) s
  exact ((GraphMorphism.identityGraph_eval (provability Γ) _ _).mp h).2

/-- Both directions concern the fixed literal Prov_Gamma predicate. -/
theorem image_membership (Γ : Carrier) (s : NumericalTuples.Point sentenceObject) :
    (∃ p : NumericalTuples.Point (proofObject Γ), (conclusion Γ).toFun p = s) ↔
      (ArithmeticLiteralModel.theoremPredicate Γ).val.Evalb (M := ℕ) ![s.val] := by
  rw [← ProofWords.fixed_provability ℕ Γ s.val,imageCarrier_eval]
  constructor
  · rintro ⟨p,hp⟩
    have he : (PredicateInterpretation.functor 𝗣𝗔 ℕ).map
        (representedArrow 𝗣𝗔 (ProofWords.conclusion Γ)) p = s :=
      (conclusion_value Γ p).symm.trans hp
    exact ⟨p.val,(PredicateInterpretation.map_class_eq_iff 𝗣𝗔 ℕ (ProofWords.conclusion Γ) p s).mp he⟩
  · rintro ⟨p,hp⟩
    let pp : NumericalTuples.Point (proofObject Γ) :=
      ⟨p,((ProofWords.conclusion Γ).support_model ℕ p s.val hp).1⟩
    refine ⟨pp,?_⟩
    rw [conclusion_value]
    exact (PredicateInterpretation.map_class_eq_iff 𝗣𝗔 ℕ (ProofWords.conclusion Γ) pp s).mpr hp

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.ProofImage
