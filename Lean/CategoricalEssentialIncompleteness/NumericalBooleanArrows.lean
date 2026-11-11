/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalBooleanObject

/-!
# Recursive Boolean functions and PER arrows

Arrows from the equality PER on `ℕ` to the Boolean PER are exactly total
recursive Boolean functions. Equality of arrows corresponds to equality of
these functions at every natural number.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace CategoricalEssentialIncompleteness
namespace NumericalPER

/-- The numerical representative of a total recursive Boolean function. -/
def booleanRepresentative (f : ℕ → Bool) (hf : Computable f) :
    Representative (discrete Set.univ) boolean where
  val n := Part.some (f n).toNat
  computable := (Primrec.dom_bool Bool.toNat).to_comp.comp hf
  total := fun _ _ ↦ Part.some_dom _
  respects := by
    intro n m a b h ha hb
    obtain rfl := h.2
    obtain rfl := Part.mem_some_iff.mp ha
    obtain rfl := Part.mem_some_iff.mp hb
    exact ⟨by cases f n <;> simp [booleanSupport], rfl⟩

/-- The PER arrow denoted by a total recursive Boolean function. -/
def booleanArrow (f : ℕ → Bool) (hf : Computable f) :
    discrete Set.univ ⟶ boolean := ofRepresentative (booleanRepresentative f hf)

/-- Equality of Boolean arrows is pointwise equality of their recursive functions. -/
theorem booleanArrow_eq_iff (f g : ℕ → Bool) (hf : Computable f) (hg : Computable g) :
    booleanArrow f hf = booleanArrow g hg ↔ f = g := by
  constructor
  · intro h
    have hv := (discrete_arrow_eq_iff (booleanRepresentative f hf)
      (booleanRepresentative g hg)).mp h
    funext n
    have he : Part.some (f n).toNat = Part.some (g n).toNat := hv n ⟨Set.mem_univ _, rfl⟩
    have hn : (f n).toNat = (g n).toNat := Part.some_injective he
    cases hf' : f n <;> cases hg' : g n <;> simp_all
  · rintro rfl
    rfl

/-- Every arrow to the Boolean PER has a total recursive Boolean representative. -/
theorem booleanArrow_surjective (f : discrete Set.univ ⟶ boolean) :
    ∃ g : ℕ → Bool, ∃ hg : Computable g, booleanArrow g hg = f := by
  induction f using Quotient.inductionOn with | _ f =>
    let v (n : ℕ) := (f.val n).get (f.total n ⟨Set.mem_univ _, rfl⟩)
    have hv : Computable v := f.computable.of_eq_tot (fun _ ↦ Part.get_mem _)
    let g : ℕ → Bool := fun n ↦ decide (v n = 1)
    have hg : Computable g := Primrec.eq.decide.to_comp.comp hv (Computable.const 1)
    refine ⟨g, hg, (discrete_arrow_eq_iff (booleanRepresentative g hg) f).mpr ?_⟩
    intro n _
    have hvalue : v n = 0 ∨ v n = 1 :=
      (f.output_supported ⟨Set.mem_univ _, rfl⟩ (Part.get_mem _)).1
    have hgvalue : (g n).toNat = v n := by
      rcases hvalue with h | h <;> simp [g, h]
    change Part.some (g n).toNat = f.val n
    rw [hgvalue]
    exact Part.some_get _

/-- Total recursive Boolean functions correspond bijectively to Boolean PER arrows. -/
def booleanArrowEquiv : {f : ℕ → Bool // Computable f} ≃
    (discrete Set.univ ⟶ boolean) :=
  Equiv.ofBijective (fun f ↦ booleanArrow f.val f.property)
    ⟨fun f g h ↦ Subtype.ext ((booleanArrow_eq_iff _ _ _ _).mp h), by
      intro f
      obtain ⟨g, hg, h⟩ := booleanArrow_surjective f
      exact ⟨⟨g, hg⟩, h⟩⟩

end NumericalPER
end CategoricalEssentialIncompleteness
