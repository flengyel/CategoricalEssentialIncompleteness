/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46FiniteSigmaOne

/-! # Finite membership statements with their exact arithmetic premises -/

@[expose] public section

noncomputable section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.FiniteSigmaOne

namespace CategoricalEssentialIncompleteness.V46.FiniteSigmaOne.StatementChecks

example (C : Carrier) : 𝚺₀.Semisentence 2 := witnessMatrix C

example (C : Carrier) : 𝗣𝗔 ⊢ finiteMembershipSentence C := finite_membership_PA C

example (R : Matrix) {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (a : M)
    (h : ∀ i < len a, ∃ w : M, R.val.Evalb ![w, nth a i]) :
    ∃ b : M, len b = len a ∧ ∀ i < len a,
      nth a i < a ∧ nth b i < b ∧ R.val.Evalb ![nth b i, nth a i] :=
  witnessVector_exists R a h

example (C : Carrier) : (finiteMembership C).val.Evalb (M := ℕ) ![0] := by
  rw [← finite_membership_model, allEntriesCondition_eval]
  simp

example {ι : Type*} [Fintype ι] (tags : ι → 𝚷₁.Semisentence 1)
    (conditions : ι → Carrier) :
    𝗣𝗔 ⊢ finiteMembershipSentence (finiteCaseCondition tags conditions) :=
  finite_tagged_membership_PA tags conditions

example {k : ℕ} (conditions : Fin k → Carrier) :
    𝗣𝗔 ⊢ finiteMembershipSentence (selectedPayloadCondition conditions) :=
  selected_tagged_membership_PA conditions

example {k : ℕ} (conditions : Fin k → Carrier)
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (a : M) :
    (selectedTaggedList conditions).val.Evalb ![a] ↔
      ∀ i < len a, ∃ j : Fin k,
        π₁ (nth a i) = ORingStructure.numeral j.val ∧
          (conditions j).val.Evalb ![π₂ (nth a i)] :=
  selectedTaggedList_model conditions a

end CategoricalEssentialIncompleteness.V46.FiniteSigmaOne.StatementChecks
