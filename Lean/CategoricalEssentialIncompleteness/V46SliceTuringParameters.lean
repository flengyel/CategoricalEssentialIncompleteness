/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SplitTuring
public import CategoricalEssentialIncompleteness.V46RestrictionSubobjects

/-! # Turing parameters and total retractions over a fixed parameter object -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.RestrictionCategory PCategoryStruct RecursionCategory

namespace CategoricalEssentialIncompleteness.V46.SliceTuringParameters

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

theorem evaluation_formula {X T Q : C} (p : X ⟶ T) (hp : isTotal p)
    (g : X ⟶ Q) (hg : isTotal g) (τ : nearProd Q Q ⟶ Q) :
    nearProd_map (partialPairing p g) (𝟙 Q) ≫ assoc T Q Q ≫ nearProd_map (𝟙 T) τ =
      partialPairing (p0 X Q ≫ p) (nearProd_map g (𝟙 Q) ≫ τ) := by
  let a := nearProd_map (partialPairing p g) (𝟙 Q)
  have ha0 : a ≫ p0 (nearProd T Q) Q = p0 X Q ≫ partialPairing p g :=
    PCategory.p0_nat _
  have ha1 : a ≫ p1 (nearProd T Q) Q = p1 X Q := by
    dsimp [a]
    rw [PCategory.nearProd_eq_partialPairing, PCategory.p1_partialPairing]
    have ht : PCategoryStruct.rst (p0 X Q ≫ partialPairing p g) =
        𝟙 (nearProd X Q) := by
      rw [PCategory.rst_comp_of_isTotal' _ (PCategory.isTotal_partialPairing hp hg),
        PCategory.p0_isTotal]
    rw [ht, Category.id_comp, Category.comp_id]
  have ha : a ≫ assoc T Q Q =
      partialPairing (p0 X Q ≫ p) (nearProd_map g (𝟙 Q)) := by
    unfold assoc
    rw [PCategory.comp_partialPairing, PCategory.comp_partialPairing]
    simp only [← Category.assoc, ha0, ha1]
    rw [Category.assoc, PCategory.p0_partialPairing_of_isTotal p hg,
      Category.assoc, PCategory.p1_partialPairing_of_isTotal g hp]
    rw [PCategory.nearProd_eq_partialPairing g (𝟙 Q), Category.comp_id]
  change a ≫ assoc T Q Q ≫ nearProd_map (𝟙 T) τ = _
  rw [← Category.assoc, ha, PCategory.partialPairing_comp_nearProd_map, Category.comp_id]

/-- The total parameter is the pair of the structural morphism and the
original Turing parameter. The equality is the slice computation equation. -/
theorem slice_parameterization {X T Q : C} (τ : nearProd Q Q ⟶ Q)
    (hτ : IsTuringMorphism τ) (p : X ⟶ T) (hp : isTotal p)
    (φ : nearProd X Q ⟶ nearProd T Q)
    (hφ : φ ≫ p0 T Q = CategoryTheory.RestrictionCategory.rst φ ≫ (p0 X Q ≫ p)) :
    ∃ a : X ⟶ nearProd T Q, isTotal a ∧ a ≫ p0 T Q = p ∧
      nearProd_map a (𝟙 Q) ≫ assoc T Q Q ≫ nearProd_map (𝟙 T) τ = φ := by
  obtain ⟨g, hg, hcode⟩ := hτ X (φ ≫ p1 T Q)
  refine ⟨partialPairing p g, PCategory.isTotal_partialPairing hp hg,
    PCategory.p0_partialPairing_of_isTotal p hg, ?_⟩
  rw [evaluation_formula p hp g hg τ, hcode]
  have ht : PCategoryStruct.rst (p0 X Q ≫ p) = 𝟙 (nearProd X Q) := by
    rw [PCategory.rst_comp_of_isTotal' _ hp, PCategory.p0_isTotal]
  have he := PCategory.eq_partialPairing_of_proj
    (h := partialPairing (p0 X Q ≫ p) (φ ≫ p1 T Q))
    (u := φ ≫ p0 T Q) (v := φ ≫ p1 T Q)
    (by rw [PCategory.p0_partialPairing, PCategory.rst_comp_p1]; exact hφ.symm)
    (by rw [PCategory.p1_partialPairing, ht, Category.id_comp])
  exact he.trans (PCategory.partialPairing_proj φ)

open RestrictionSubobjects

/-- A total embedding in the Turing object gives a total embedding over T;
its monic partial inverse also lies over T on its domain of definition. -/
theorem total_retract_over (inverses : MonoInverses C) {X T Q : C}
    (p : X ⟶ T) (hp : isTotal p) (m : X ⟶ Q) (hm : isTotal m)
    (r : Q ⟶ X) (hmr : m ≫ r = 𝟙 X) :
    ∃ (j : X ⟶ nearProd T Q) (s : nearProd T Q ⟶ X),
      isTotal j ∧ j ≫ p0 T Q = p ∧ j ≫ s = 𝟙 X ∧ s ≫ j =
        CategoryTheory.RestrictionCategory.rst s ∧
      s ≫ p = CategoryTheory.RestrictionCategory.rst s ≫ p0 T Q := by
  let j := partialPairing p m
  have hj : isTotal j := PCategory.isTotal_partialPairing hp hm
  have hj0 : j ≫ p0 T Q = p := PCategory.p0_partialPairing_of_isTotal p hm
  have hjr : j ≫ (p1 T Q ≫ r) = 𝟙 X := by
    rw [← Category.assoc, PCategory.p1_partialPairing_of_isTotal m hp, hmr]
  let j' : (⟨X⟩ : Tot C) ⟶ ⟨nearProd T Q⟩ := ⟨j, hj⟩
  have : Mono j' := by
    constructor
    intro Z f g he
    apply WideSubcategory.hom_ext
    have hh := congrArg (fun k => k.hom ≫ (p1 T Q ≫ r)) he
    change (f.hom ≫ j) ≫ (p1 T Q ≫ r) = (g.hom ≫ j) ≫ (p1 T Q ≫ r) at hh
    simpa only [Category.assoc, hjr, Category.comp_id] using hh
  let s := inverse inverses j'
  have hs : s ≫ j = CategoryTheory.RestrictionCategory.rst s := inverse_hom inverses j'
  refine ⟨j, s, hj, hj0, hom_inverse inverses j', hs, ?_⟩
  rw [← hj0, ← Category.assoc, hs]

end CategoricalEssentialIncompleteness.V46.SliceTuringParameters
