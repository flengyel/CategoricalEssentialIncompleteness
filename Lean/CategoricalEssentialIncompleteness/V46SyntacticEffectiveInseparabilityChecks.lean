/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticEffectiveInseparability

/-! # The binary productive morphism of Montagna's Remark 3.1 -/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.PCategoryStruct
open CategoryTheory.RestrictionCategory (isTotal)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedTuringMorphism
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.EffectiveInseparability.Checks

theorem productive_in_PA :
    let U := omegaObject 𝗣𝗔
    let τ := typedTau 𝗣𝗔
    (∀ (W : CodedProgramCategory 𝗣𝗔) (e : Idem U), ∃ h : W ⟶ U,
      isTotal h ∧ nearProd_map h (𝟙 U) ≫ τ = p1 W U ≫ e.hom) ∧
      ∃ (a b : Idem U) (m : nearProd U U ⟶ U), a.hom ≫ b.hom = 0 ∧ isTotal m ∧
        ∀ {W : CodedProgramCategory 𝗣𝗔} (e f : Idem U) (h k : W ⟶ U),
          isTotal h → nearProd_map h (𝟙 U) ≫ τ = p1 W U ≫ e.hom →
          isTotal k → nearProd_map k (𝟙 U) ≫ τ = p1 W U ≫ f.hom →
          a.hom ≫ e.hom = a.hom → b.hom ≫ f.hom = b.hom → e.hom ≫ f.hom = 0 →
          (partialPairing h k ≫ m) ≫ e.hom = 0 ∧ (partialPairing h k ≫ m) ≫ f.hom = 0 := by
  obtain ⟨indices, a, b, m, ab, total, productive⟩ := syntactic_pair 𝗣𝗔
  exact ⟨indices, a, b, m, congrArg Idem.hom ab, total, fun e f h k th ih tk ik ea fb dis =>
    productive e f h k ⟨th, ih⟩ ⟨tk, ik⟩ ea fb (Idem.ext dis)⟩

end CategoricalEssentialIncompleteness.V46.EffectiveInseparability.Checks

open CategoricalEssentialIncompleteness.V46.EffectiveInseparability

#print axioms reduction
#print axioms exists_productive_pair
#print axioms syntactic_pair
#print axioms Checks.productive_in_PA
