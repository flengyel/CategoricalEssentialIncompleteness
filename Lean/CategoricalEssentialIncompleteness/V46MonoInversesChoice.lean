/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RestrictionSubobjects

/-! # Weak choice from partial inverses of total monomorphisms -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.RestrictionSubobjects

variable {C : Type u} [Category.{v} C] [RestrictionCategory C] [Splits C]
theorem section_of_partial_mono (inverses : MonoInverses C)
    {X Y : C} (p : X ⟶ Y) (hp : PartialMono p) :
    ∃ s : Y ⟶ X, SectionOf p s := by
  obtain ⟨A, m, r, hm, hmr, hrm⟩ := Splits.splitting (Idem.ofRestrict p)
  change r ≫ m = rst p at hrm
  have hma : m ≫ rst p = m := by
    rw [← hrm, ← Category.assoc, hmr, Category.id_comp]
  have hq : isTotal (m ≫ p) := by
    change rst (m ≫ p) = 𝟙 A
    rw [rst_comp_rst_right, hma]
    exact hm
  let A' : Tot C := ⟨A⟩
  let Y' : Tot C := ⟨Y⟩
  let q : A' ⟶ Y' := ⟨m ≫ p, hq⟩
  have : Mono q := by
    constructor
    intro Z f g he
    apply WideSubcategory.hom_ext
    have hh : (f.hom ≫ m) ≫ p = (g.hom ≫ m) ≫ p := by
      have hh := congrArg (fun k => k.hom) he
      change f.hom ≫ (m ≫ p) = g.hom ≫ (m ≫ p) at hh
      simpa only [Category.assoc] using hh
    have hc := hp (f.hom ≫ m) (g.hom ≫ m) hh
    simp only [Category.assoc, hma] at hc
    have hd := congrArg (fun k => k ≫ r) hc
    dsimp only [A'] at f g hd ⊢
    simpa only [Category.assoc, hmr, Category.comp_id] using hd
  let s' := inverse inverses q
  have hs' : s' ≫ q.hom = rst s' := inverse_hom inverses q
  have hqs' : q.hom ≫ s' = 𝟙 A := hom_inverse inverses q
  have hfix : q.hom ≫ rst s' = q.hom := by
    rw [← hs', ← Category.assoc, hqs', Category.id_comp]
  have hrep : r ≫ q.hom = p := by
    change r ≫ (m ≫ p) = p
    rw [← Category.assoc, hrm, rst_comp_self]
  refine ⟨s' ≫ m, ?_⟩
  constructor
  · calc
      (s' ≫ m) ≫ p = s' ≫ q.hom := Category.assoc _ _ _
      _ = rst s' := hs'
      _ = rst (s' ≫ m) := (rst_comp_of_isTotal s' hm).symm
  · calc
      p ≫ (s' ≫ m) ≫ p = p ≫ (s' ≫ q.hom) := by
        simp only [q, Category.assoc]
      _ = p ≫ rst s' := congrArg (fun k => p ≫ k) hs'
      _ = (r ≫ q.hom) ≫ rst s' := by rw [hrep]
      _ = r ≫ q.hom := by rw [Category.assoc, hfix]
      _ = p := hrep

theorem weakChoice (inverses : MonoInverses C) : WeakChoice C :=
  ⟨section_of_partial_mono inverses⟩

end CategoricalEssentialIncompleteness.V46.RestrictionSubobjects
