/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryBooleanTheoryClosure
public import CategoricalEssentialIncompleteness.V46BooleanFibers

/-! # A closed, consistent, complete sentence theory from a Boolean valuation -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (d : X ⟶ Two D)

def sentenceValue : S.sentenceObject ⟶ Two D := S.sentenceInclusion ≫ valuation S d

def sentenceTheory : Subobject S.sentenceObject := Two.fiberSubobject (sentenceValue S d) true

@[reassoc] theorem sentence_negation_value :
    S.sentenceNegation ≫ sentenceValue S d = Two.unary Bool.not (sentenceValue S d) := by
  rw [sentenceValue, ← Category.assoc, S.sentenceNegation_inclusion,
    Category.assoc, negation_value, Two.comp_unary]

theorem refutation_fiber :
    (Subobject.pullback S.sentenceNegation).obj (sentenceTheory S d) =
      Two.fiberSubobject (sentenceValue S d) false := by
  rw [sentenceTheory, ← Two.fiberSubobject_comp, sentence_negation_value,
    Two.not_fiber_true]

theorem sentence_consistent :
    sentenceTheory S d ⊓ (Subobject.pullback S.sentenceNegation).obj (sentenceTheory S d) =
      ⊥ := by
  rw [refutation_fiber]
  exact (Two.boundFibers_isCompl (sentenceValue S d)).symm.inf_eq_bot

theorem sentence_complete :
    sentenceTheory S d ⊔ (Subobject.pullback S.sentenceNegation).obj (sentenceTheory S d) =
      ⊤ := by
  rw [refutation_fiber]
  exact (Two.boundFibers_isCompl (sentenceValue S d)).symm.sup_eq_top

variable (proofs : (A : Subobject S.sentenceObject) →
  Endofunctor.Algebra (S.logicalRules A.arrow).inference)
variable (initial : ∀ A, IsInitial (proofs A))

include initial in
theorem sentence_closed :
    FirstOrderReflection.generated proofs (sentenceTheory S d) = sentenceTheory S d := by
  have ha : (sentenceTheory S d).arrow ≫ S.sentenceInclusion ≫ valuation S d =
      Two.constant _ true := Two.fiber_arrow_value (sentenceValue S d) true
  obtain ⟨w, hw⟩ := (firstOrder_least_image S.logicalAxioms S.sentenceInclusion
    (sentenceTheory S d).arrow S.quantifierConstructor S.implicationConstructor
    (proofs (sentenceTheory S d)) (initial _)).2
      (trueInclusion S d) (truth_closed S d _ ha)
  have hf : imageSubobject (proofs (sentenceTheory S d)).a.hom ≤
      Two.fiberSubobject (valuation S d) true := Subobject.mk_le_mk_of_comm w hw
  apply le_antisymm
  · rw [FirstOrderReflection.generated_eq_pullback]
    change (Subobject.pullback S.sentenceInclusion).obj
      (imageSubobject (proofs (sentenceTheory S d)).a.hom) ≤ _
    have hb := (Subobject.pullback S.sentenceInclusion).monotone hf
    simpa only [← Two.fiberSubobject_comp, sentenceTheory, sentenceValue] using hb
  · exact FirstOrderReflection.extensive proofs (sentenceTheory S d)

end CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation
