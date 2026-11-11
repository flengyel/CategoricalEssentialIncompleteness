/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticUnaryImage
public import CategoricalEssentialIncompleteness.V46NumericalArithmeticRules
public import CategoricalEssentialIncompleteness.V46NumericalRealization
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! # Sentence derivations retain the original numerical proof word -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SentenceProofCodes
open Coordinates
local notation "U" => NumericalUnderlying.functor

abbrev proofPredicate (Γ : Carrier) : PredicateCategory 𝗧𝗔 := NumericalDerivation.successfulCodes (Rules.rules Γ)
abbrev allProofs (Γ : Carrier) := NumericalDerivation.codeObject (Rules.rules Γ)
abbrev allAlgebra (Γ : Carrier) := NumericalDerivation.codeAlgebra (Rules.rules Γ)
def allInitial (Γ : Carrier) : IsInitial (allAlgebra Γ) := NumericalDerivation.codeInitial (Rules.rules Γ)
abbrev allConclusion (Γ : Carrier) := NumericalDerivation.codeConclusion (Rules.rules Γ)
abbrev chosenPullback (Γ : Carrier) := pullback (allConclusion Γ) numericalSyntax.sentenceInclusion

def proofProjection (Γ : Carrier) : chosenPullback Γ ⟶
    NumericalCoordinates.predicateObject (proofPredicate Γ) :=
  pullback.fst (allConclusion Γ) numericalSyntax.sentenceInclusion

instance proofProjection_mono (Γ : Carrier) : Mono (proofProjection Γ) := by
  dsimp only [proofProjection]
  infer_instance

/-- Only the original proof word is stored. The pullback point and all
computation records occur inside the existential image predicate. -/
def object (Γ : Carrier) : NumericalTuples.Object :=
  UnaryImage.object (C := proofPredicate Γ) (proofProjection Γ)

def inclusion (Γ : Carrier) : object Γ ⟶ allProofs Γ :=
  UnaryImage.inclusion (C := proofPredicate Γ) (proofProjection Γ)

def pullbackIso (Γ : Carrier) : chosenPullback Γ ≅ object Γ :=
  UnaryImage.iso (C := proofPredicate Γ) (proofProjection Γ)

def conclusion (Γ : Carrier) : object Γ ⟶ numericalSyntax.sentenceObject :=
  (pullbackIso Γ).inv ≫ pullback.snd (allConclusion Γ) numericalSyntax.sentenceInclusion

theorem dimension (Γ : Carrier) : (object Γ).dimension = 1 := rfl

abbrev inclusion_value (Γ : Carrier) (p : NumericalTuples.Point (object Γ)) :=
  UnaryImage.inclusion_value (C := proofPredicate Γ) (proofProjection Γ) p

@[reassoc] theorem pullbackIso_inclusion (Γ : Carrier) :
    (pullbackIso Γ).hom ≫ inclusion Γ =
      pullback.fst (allConclusion Γ) numericalSyntax.sentenceInclusion :=
  UnaryImage.iso_inclusion (C := proofPredicate Γ) (proofProjection Γ)

@[reassoc] theorem pullbackIso_conclusion (Γ : Carrier) :
    (pullbackIso Γ).hom ≫ conclusion Γ =
      pullback.snd (allConclusion Γ) numericalSyntax.sentenceInclusion := by
  simp only [conclusion,Iso.hom_inv_id_assoc]

theorem isPullback (Γ : Carrier) :
    IsPullback (inclusion Γ) (conclusion Γ) (allConclusion Γ) numericalSyntax.sentenceInclusion := by
  apply (IsPullback.of_hasPullback (allConclusion Γ) numericalSyntax.sentenceInclusion).of_iso
    (pullbackIso Γ) (Iso.refl (allProofs Γ)) (Iso.refl numericalSyntax.sentenceObject)
    (Iso.refl numericalSyntax.algebra.a.2)
  · simpa only [Iso.refl_hom,Category.comp_id] using (pullbackIso_inclusion Γ).symm
  · simpa only [Iso.refl_hom,Category.comp_id] using (pullbackIso_conclusion Γ).symm
  · simp
  · simp

theorem conclusion_square (Γ : Carrier) :
    inclusion Γ ≫ allConclusion Γ = conclusion Γ ≫ numericalSyntax.sentenceInclusion :=
  (isPullback Γ).w

/-- The support is exactly the set of original valid derivation words
whose conclusion has an actual sentence lift. -/
theorem membership (Γ : Carrier) (p : ℕ) :
    (object Γ).support p ↔ ∃ q : NumericalTuples.Point (allProofs Γ), q.val = p ∧
      ∃ s : NumericalTuples.Point numericalSyntax.sentenceObject,
        numericalSyntax.sentenceInclusion.toFun s = (allConclusion Γ).toFun q := by
  refine (UnaryImage.membership (C := proofPredicate Γ) (proofProjection Γ) p).trans ?_
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨(proofProjection Γ).toFun z,hz,
      (pullback.snd (allConclusion Γ) numericalSyntax.sentenceInclusion).toFun z,?_⟩
    exact (congrArg (fun f => f.toFun z)
      (pullback.condition (f := allConclusion Γ) (g := numericalSyntax.sentenceInclusion))).symm
  · rintro ⟨q,hq,s,hs⟩
    obtain ⟨z,hz,_⟩ := Types.exists_of_isPullback
      ((IsPullback.of_hasPullback (allConclusion Γ) numericalSyntax.sentenceInclusion).map (U)) q s hs.symm
    exact ⟨z,(congrArg Subtype.val hz).trans hq⟩

/-- The regular image is the sentence pullback of the generated formula
theory, now for the carrier that stores the original word alone. -/
theorem generated_sentence_image (Γ : Carrier) :
    imageSubobject (conclusion Γ) =
      (Subobject.pullback numericalSyntax.sentenceInclusion).obj (imageSubobject (allConclusion Γ)) := by
  exact (imageSubobject_iso_comp (pullbackIso Γ).inv
    (pullback.snd (allConclusion Γ) numericalSyntax.sentenceInclusion)).trans
      (NumericalRealization.generated_theory numericalSyntax (Rules.axioms Γ)).2.2.2

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SentenceProofCodes
