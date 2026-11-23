/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46JaniczakCoding
public import CategoricalEssentialIncompleteness.V46JaniczakTheories
public import CategoricalEssentialIncompleteness.NumericalInseparability

/-!
# Recursive separators from decidable extensions

A decision algorithm for the consequences of a consistent extension separates the positive and negative indices by querying the finite class-size sentences.
-/

@[expose] public section

set_option autoImplicit false

namespace Janiczak

/-- An algorithm decides consequence if it gives the right answer on every formula code. -/
def DecidableTheorems (T : Set Formula) :=
  ∃ d : ℕ → Bool, Computable d ∧ ∀ p : Formula, d p.code = true ↔ Consequence T p

/-- Every consistent extension in the same first-order language has undecidable theoremhood. -/
def EssentiallyUndecidable (T : Set Formula) :=
  ∀ U : Set Formula, T ⊆ U → Consistent U → ¬ DecidableTheorems U

theorem separator_of_decidable_extension {P N : Set ℕ} {U : Set Formula}
    (he : Signed P N ⊆ U) (hc : Consistent U) (hd : DecidableTheorems U) :
    ∃ D : Set ℕ, ComputablePred (· ∈ D) ∧ P ⊆ D ∧ Disjoint D N := by
  obtain ⟨d, hdc, hspec⟩ := hd
  let D : Set ℕ := {i | d (Formula.sizeSentence i).code = true}
  refine ⟨D, ComputablePred.computable_iff.mpr ⟨_, hdc.comp Formula.primrec_sizeSentence.to_comp,
    rfl⟩, ?_, Set.disjoint_left.mpr ?_⟩
  · exact fun i hi ↦ (hspec _).mpr (Consequence.of_mem (he (Signed.pos hi)))
  · intro i hi hn
    exact Consequence.compatible hc ((hspec _).mp hi) (Consequence.of_mem (he (Signed.neg hn)))

/-- Recursive inseparability of the numerical pair precludes a decision algorithm
in every consistent extension of the actual signed equivalence-relation theory. -/
theorem essentiallyUndecidable_of_inseparable {P N : Set ℕ}
    (h : CategoricalEssentialIncompleteness.Numerical.RecursivelyInseparable P N) :
    EssentiallyUndecidable (Signed P N) :=
  fun _ he hc hd ↦ h.2 (separator_of_decidable_extension he hc hd)

end Janiczak
