/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46FiniteSigmaOne

/-! # Finite list membership with a specified selector graph -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace CategoricalEssentialIncompleteness.V46.FiniteSigmaOne

/-- Insert a numeral in the output position of the given graph. -/
def selectorBranch (L : 𝚺₁.Semisentence 2) (j : ℕ) : Carrier := .mkSigma
  “x. !L.val x !!(numeralTerm j)”

/-- One list entry satisfies a condition whose index its selector actually returns. -/
def selectedEntry {s : ℕ} (L : 𝚺₁.Semisentence 2) (D : Fin s → Carrier) : Carrier :=
  .mkSigma (Finset.udisj (fun j : Fin s => (selectorBranch L j.val).val ⋏ (D j).val)) (by
    simp only [Hierarchy.finset_udisj_iff, Hierarchy.and_iff]
    intro j
    exact ⟨(selectorBranch L j.val).sigma_prop, (D j).sigma_prop⟩)

theorem selectedEntry_eval {s : ℕ} (L : 𝚺₁.Semisentence 2) (D : Fin s → Carrier)
    {M : Type*} [ORingStructure M] (x : M) :
    (selectedEntry L D).val.Evalb ![x] ↔
      ∃ j : Fin s, L.val.Evalb ![x, ORingStructure.numeral j.val] ∧ (D j).val.Evalb ![x] := by
  simp [selectedEntry, selectorBranch, numeralTerm]

theorem selected_entries_model {s : ℕ} (L : 𝚺₁.Semisentence 2) (D : Fin s → Carrier)
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (a : M) :
    (finiteMembership (selectedEntry L D)).val.Evalb ![a] ↔
      ∀ i < len a, ∃ j : Fin s,
        L.val.Evalb ![nth a i, ORingStructure.numeral j.val] ∧ (D j).val.Evalb ![nth a i] := by
  rw [← finite_membership_model, allEntriesCondition_eval]
  simp only [selectedEntry_eval]

theorem selected_entries_PA {s : ℕ} (L : 𝚺₁.Semisentence 2) (D : Fin s → Carrier) :
    𝗣𝗔 ⊢ finiteMembershipSentence (selectedEntry L D) :=
  finite_membership_PA _

end CategoricalEssentialIncompleteness.V46.FiniteSigmaOne
