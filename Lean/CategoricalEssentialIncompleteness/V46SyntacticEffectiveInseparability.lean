/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46EffectiveInseparability
public import CategoricalEssentialIncompleteness.SyntacticModel

/-! # Montagna's effectively inseparable domains in the unprimed syntactic category -/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.PCategoryStruct
open CategoryTheory.RestrictionCategory (isTotal)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedTuringMorphism
open FailureOfComposition.TypedRecursionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.EffectiveInseparability

/-- Every domain has indices in the chosen numbering. A single total binary
morphism is productive for all disjoint extensions of the two domains. -/
theorem syntactic_pair (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    (∀ (W : CodedProgramCategory T) (e : Idem (omegaObject T)),
      ∃ h : W ⟶ omegaObject T, Index (typedTau T) e h) ∧
    ∃ (c d : Idem (omegaObject T)) (m : nearProd (omegaObject T) (omegaObject T) ⟶ omegaObject T),
      c ⊓ d = ⊥ ∧ isTotal m ∧
      ∀ {W : CodedProgramCategory T} (e f : Idem (omegaObject T)) (h k : W ⟶ omegaObject T),
        Index (typedTau T) e h → Index (typedTau T) f k → c ≤ e → d ≤ f → e ⊓ f = ⊥ →
          (partialPairing h k ≫ m) ≫ e.hom = 0 ∧ (partialPairing h k ≫ m) ≫ f.hom = 0 :=
  ⟨fun W e => typedTau_isTuringMorphism T W (p1 W (omegaObject T) ≫ e.hom),
    exists_productive_pair (typedTau T) (omegaProductIso T)⟩

end CategoricalEssentialIncompleteness.V46.EffectiveInseparability
