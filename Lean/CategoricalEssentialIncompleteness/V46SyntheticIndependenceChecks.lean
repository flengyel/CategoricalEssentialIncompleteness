/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntheticIndependence

/-! # The formal systems and enumeration in Kirst and Peters' Theorem 20 -/

@[expose] public section

set_option autoImplicit false

namespace CategoricalEssentialIncompleteness.V46.SyntheticComputability.Checks

universe u

theorem admits_independent_sentence {S : Type u} {neg : S → S}
    (θ : ℕ → PartialFunction ℕ ℕ)
    (enumeration : ∀ g : PartialFunction ℕ ℕ, ∃ c, ∀ x y,
      (∃ s, (θ c).run x s = some y) ↔ ∃ t, g.run x t = some y)
    (T : FormalSystem S neg)
    (separates : ∃ r : ℕ → S, ∀ n,
      ((∃ s, (θ n).run n s = some 1) → T.provable (r n)) ∧
      ((∃ s, (θ n).run n s = some 0) → T.provable (neg (r n)))) :
    ∀ U : FormalSystem S neg, (∀ φ, T.provable φ → U.provable φ) →
      ∃ φ, ¬ U.provable φ ∧ ¬ U.provable (neg φ) := by
  rintro U extendsT
  obtain ⟨r, hr⟩ := separates
  obtain ⟨c, hc⟩ := independent_in_extension θ enumeration T r
    (fun n ↦ (hr n).1) (fun n ↦ (hr n).2) U extendsT
  exact ⟨r c, hc⟩

end CategoricalEssentialIncompleteness.V46.SyntheticComputability.Checks

open CategoricalEssentialIncompleteness.V46.SyntheticComputability

#print axioms independent_in_extension
#print axioms Checks.admits_independent_sentence
