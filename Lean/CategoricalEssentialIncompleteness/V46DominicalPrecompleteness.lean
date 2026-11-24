/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DominicalDiagonal

/-!
# Bernardi's categorical fixed-point theorem

Bernardi, §3, Definition 1 and Theorem 1, uses a restriction domain on
the near product of an object with itself. A totalizer for a partial
endomorphism agrees with it modulo that domain wherever the given
endomorphism is defined. Totalizing the Turing diagonal followed by a
given morphism and taking an index of the totalizer gives the fixed point.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.DiPaolaHeller CategoryTheory.PCategoryStruct
open CategoryTheory.PCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.DominicalPrecompleteness

universe v u
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [HasZeroMorphisms C]

/-- Bernardi's precompleteness condition on a relation domain. -/
def Precomplete {X : C} (η : Idem (nearProd X X)) : Prop :=
  ∀ ψ : X ⟶ X, ∃ h : X ⟶ X, DiPaolaHeller.IsTotal h ∧
    rst (partialPairing ψ h ≫ η.hom) = rst ψ

theorem fixed_point {X : C} (τ : nearProd X X ⟶ X) (universal : IsTuringMorphism τ)
    (η : Idem (nearProd X X)) (complete : Precomplete η) (φ : X ⟶ X) :
    ∃ g : X ⟶ X, DiPaolaHeller.IsTotal g ∧
      rst (g ≫ partialPairing φ (𝟙 X) ≫ η.hom) = rst (g ≫ φ) := by
  let D := diag X ≫ τ
  obtain ⟨h, hTotal, agrees⟩ := complete (D ≫ φ)
  obtain ⟨w, wTotal, diagonal⟩ := DominicalDiagonal.fixed_source_diagonal τ universal h
  have wd : w ≫ D = w ≫ h := diagonal
  refine ⟨w ≫ h, wTotal.comp hTotal, ?_⟩
  have eq : (w ≫ h) ≫ partialPairing φ (𝟙 X) = w ≫ partialPairing (D ≫ φ) h := by
    simp only [comp_partialPairing, Category.comp_id, ← Category.assoc, wd]
  calc rst ((w ≫ h) ≫ partialPairing φ (𝟙 X) ≫ η.hom)
      = rst (w ≫ partialPairing (D ≫ φ) h ≫ η.hom) := by
        rw [← Category.assoc, eq, Category.assoc]
    _ = rst (w ≫ (D ≫ φ)) := by
      rw [rst_comp_rst_right' w (partialPairing (D ≫ φ) h ≫ η.hom), agrees,
        ← rst_comp_rst_right']
    _ = rst ((w ≫ h) ≫ φ) := by rw [← Category.assoc, wd]

/-- Di Paola and Heller, Proposition 6.6. Every nonzero domain receives
a total morphism from each object. -/
theorem exists_total_in_domain [HasChoice C] (hd : Dominical C) {X : C}
    (e : Idem X) (ne : e.hom ≠ 0) (Y : C) :
    ∃ f : Y ⟶ X, DiPaolaHeller.IsTotal f ∧ f ≫ e.hom = f := by
  let k := nearProd_map e.hom (𝟙 Y)
  let p := k ≫ p1 X Y
  obtain ⟨s, sectionOf⟩ := HasChoice.exists_isSection p
  have total : DiPaolaHeller.IsTotal s := by
    intro W t killed
    let u := nearProd_map e.hom t
    have uk : u ≫ k = u := by
      simp only [u, k, nearProd_comp, e.idem, Category.comp_id]
    have proj : u ≫ p1 X Y = (nearProd_map e.hom (𝟙 W) ≫ p1 X W) ≫ t := by
      dsimp only [u]
      rw [← nearProd_comp_id_id_comp e.hom t, Category.assoc, p1_nat, Category.assoc]
    have up : u ≫ p = u ≫ p1 X Y := by
      dsimp only [p]
      rw [← Category.assoc, uk]
    have ups : (u ≫ p) ≫ s = 0 := by rw [up, proj, Category.assoc, killed, comp_zero]
    have upz : u ≫ p = 0 := by
      calc u ≫ p = u ≫ p ≫ s ≫ p := by rw [sectionOf.comp_self]
           _ = 0 := by rw [← Category.assoc, ← Category.assoc, ups, zero_comp]
    have uz : u = 0 := hd.isTotal_p1 X Y u (up ▸ upz)
    exact ((hd.nearProd_eq_zero_iff e.hom t).mp uz).resolve_left ne
  have sp : s ≫ p = 𝟙 Y := sectionOf.comp_eq_rst.trans ((hd.isTotal_iff_rst_eq_id s).mp total)
  have sk : DiPaolaHeller.IsTotal (s ≫ k) := by
    intro Z r zero
    have h := congrArg (fun l => l ≫ p1 X Y) zero
    simpa only [Category.assoc, show s ≫ k ≫ p1 X Y = 𝟙 Y from sp,
      Category.comp_id, zero_comp] using h
  refine ⟨(s ≫ k) ≫ p0 X Y, sk.comp (hd.isTotal_p0 X Y), ?_⟩
  simp only [k, Category.assoc, p0_nat, e.idem]

end CategoricalEssentialIncompleteness.V46.DominicalPrecompleteness
