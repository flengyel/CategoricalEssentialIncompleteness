/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import PCats.Recursion

/-! # Turing objects and total sections of retractions -/

@[expose] public section

open CategoryTheory PCategoryStruct RecursionCategory RestrictionCategory
universe v u

namespace CategoricalEssentialIncompleteness.V46

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

/-- A single endoevaluator and retractions suffice for evaluators of all input and output types. -/
theorem turingObject_iff (U : C) :
    (∀ A B : C, ∃ τ : nearProd U A ⟶ B, IsTuringMorphism τ) ↔
      (∃ τ : nearProd U U ⟶ U, IsTuringMorphism τ) ∧
        ∀ X : C, ∃ (m : X ⟶ U) (r : U ⟶ X), isTotal m ∧ m ≫ r = 𝟙 X := by
  constructor
  · intro typed
    refine ⟨typed U U, ?_⟩
    intro X
    obtain ⟨eval, he⟩ := typed U X
    obtain ⟨m, hm, h⟩ := he X (p0 X U)
    refine ⟨m, diag U ≫ eval, hm, ?_⟩
    have eqn := congrArg (fun k => partialPairing (𝟙 X) m ≫ k) h
    rw [← Category.assoc, PCategory.partialPairing_comp_nearProd_map,
      Category.id_comp, Category.comp_id, PCategory.p0_partialPairing_of_isTotal _ hm] at eqn
    rwa [← Category.assoc, PCategory.diag_nat]
  · rintro ⟨⟨τ, hτ⟩, retract⟩ A B
    obtain ⟨mA, rA, _, hrA⟩ := retract A
    obtain ⟨mB, rB, _, hrB⟩ := retract B
    refine ⟨nearProd_map (𝟙 U) mA ≫ τ ≫ rB, ?_⟩
    intro Z f
    obtain ⟨g, hg, h⟩ := hτ Z (nearProd_map (𝟙 Z) rA ≫ f ≫ mB)
    refine ⟨g, hg, ?_⟩
    have swap : nearProd_map g (𝟙 A) ≫ nearProd_map (𝟙 U) mA =
        nearProd_map (𝟙 Z) mA ≫ nearProd_map g (𝟙 U) := by
      simp only [PCategory.nearProd_comp, Category.comp_id, Category.id_comp]
    calc
      _ = nearProd_map (𝟙 Z) mA ≫ (nearProd_map g (𝟙 U) ≫ τ) ≫ rB := by
        rw [← Category.assoc, swap]
        simp only [Category.assoc]
      _ = f := by
        rw [h]
        have cancel : nearProd_map (𝟙 Z) mA ≫ nearProd_map (𝟙 Z) rA = 𝟙 _ := by
          rw [PCategory.nearProd_comp, Category.comp_id, hrA, PCategory.nearProd_id]
        simpa only [Category.assoc] using
          (show (nearProd_map (𝟙 Z) mA ≫ nearProd_map (𝟙 Z) rA) ≫ f ≫ (mB ≫ rB) = f by
            rw [cancel, hrB, Category.comp_id, Category.id_comp])

end CategoricalEssentialIncompleteness.V46
