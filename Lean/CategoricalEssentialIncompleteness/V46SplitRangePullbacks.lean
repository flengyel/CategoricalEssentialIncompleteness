/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SplitRangeFactorization
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Pullback stability of the range factorization

For a total morphism \(f:X\to Y\) and a restriction monic \(m:B\to Y\)
with partial inverse \(r\), split the restriction idempotent of \(rf\).
Its inclusion is the pullback of \(m\) along \(f\). If \(f\) has full range,
the other projection has full range as well. These statements give the
stability assertion in Cockett, Guo and Hofstra, Theorem 4.7 of
*Range categories I*, cited in Appendix A.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.V46 (TotalCategory total_split_mono)

namespace CategoricalEssentialIncompleteness.V46.RangeOperation

universe v u
variable {C : Type u} [Category.{v} C] [RestrictionCategory C] [Splits C]
variable (R : RangeOperation C)

private theorem pullback_of_factorization {D : Type*} [Category* D] {P X B Y : D}
    {j : P ⟶ X} {g : P ⟶ B} {f : X ⟶ Y} {m : B ⟶ Y} [Mono j] [Mono m]
    (square : j ≫ f = g ≫ m)
    (lifts : ∀ {W : D} (a : W ⟶ X) (b : W ⟶ B), a ≫ f = b ≫ m → ∃ d : W ⟶ P, d ≫ j = a) :
    IsPullback j g f m := by
  refine IsPullback.of_isLimit (c := PullbackCone.mk j g square) ?_
  apply PullbackCone.isLimitAux'
  intro s
  let d := (lifts s.fst s.snd s.condition).choose
  have dj : d ≫ j = s.fst := (lifts s.fst s.snd s.condition).choose_spec
  refine ⟨d, dj, (cancel_mono m).mp ?_, fun h _ => (cancel_mono j).mp (h.trans dj.symm)⟩
  change (d ≫ g) ≫ m = s.snd ≫ m
  rw [Category.assoc, ← square, ← Category.assoc, dj, s.condition]

private theorem pullback_exists {X B Y : TotalCategory C} (f : X ⟶ Y) (m : B ⟶ Y)
    (hm : restrictionMonics m) :
    ∃ (P : TotalCategory C) (j : P ⟶ X) (g : P ⟶ B),
      IsPullback j g f m ∧ restrictionMonics j ∧ (R.fullRange f → R.fullRange g) := by
  have := restrictionMonics_mono hm
  obtain ⟨r, mr, rm⟩ := hm
  let a := Idem.ofRestrict (f.hom ≫ r)
  obtain ⟨I, u, v, hu, uv, vu⟩ := Splits.splitting a
  change v ≫ u = rst (f.hom ≫ r) at vu
  let P : TotalCategory C := ⟨I⟩
  let j : P ⟶ X := ⟨u, hu⟩
  have fixed : u ≫ rst (f.hom ≫ r) = u := by rw [← vu, ← Category.assoc, uv, Category.id_comp]
  have eq : (u ≫ f.hom ≫ r) ≫ m.hom = u ≫ f.hom := by
    calc _ = u ≫ f.hom ≫ rst r := by simp only [Category.assoc, rm]
         _ = (u ≫ rst (f.hom ≫ r)) ≫ f.hom := by rw [Category.assoc, rst_comp]
         _ = _ := by rw [fixed]
  let g : P ⟶ B := ⟨u ≫ f.hom ≫ r, total_of_comp_total _ m.hom (by
    rw [eq]
    exact isTotal_comp hu f.property)⟩
  have square : j ≫ f = g ≫ m := WideSubcategory.hom_ext _ eq.symm
  have hj : restrictionMonics j := ⟨v, uv, vu.trans (splitter_restriction hu (e := a) vu).symm⟩
  have := restrictionMonics_mono hj
  refine ⟨P, j, g, pullback_of_factorization square ?_, hj, ?_⟩
  · intro W x b comm
    have sq : x.hom ≫ f.hom = b.hom ≫ m.hom := congrArg (fun k : W ⟶ Y => k.hom) comm
    have xb : x.hom ≫ f.hom ≫ r = b.hom := by
      rw [← Category.assoc, sq, Category.assoc, mr, Category.comp_id]
    have total : rst (x.hom ≫ f.hom ≫ r) = 𝟙 W.obj := by rw [xb]; exact b.property
    have lift_eq : (x.hom ≫ v) ≫ u = x.hom := by
      rw [Category.assoc, vu, ← rst_comp, total, Category.id_comp]
    exact ⟨⟨x.hom ≫ v, total_of_comp_total _ u (by rw [lift_eq]; exact x.property)⟩,
      WideSubcategory.hom_ext _ lift_eq⟩
  · intro hf
    have vg : v ≫ g.hom = f.hom ≫ r := by
      change v ≫ u ≫ f.hom ≫ r = _
      rw [← Category.assoc, vu, rst_comp_self]
    have vFull := R.range_of_section u uv
    change (R.range g.hom).hom = _
    rw [← R.range_comp_of_full g.hom vFull, vg, R.range_comp_of_full r hf]
    exact R.range_of_section m.hom mr

/-- The factorization is stable along restriction monics. Such pullbacks
exist, and the assertion holds for every choice of pullback square. -/
theorem stableFactorization :
    OrthogonalFactorizationSystem R.fullRange restrictionMonics ∧
    (∀ {X B Y : TotalCategory C} (f : X ⟶ Y) (m : B ⟶ Y),
      restrictionMonics m → HasPullback f m) ∧
    (∀ {P X B Y : TotalCategory C} {j : P ⟶ X} {g : P ⟶ B} {f : X ⟶ Y} {m : B ⟶ Y},
      IsPullback j g f m → restrictionMonics m →
        restrictionMonics j ∧ (R.fullRange f → R.fullRange g)) := by
  refine ⟨R.factorizationSystem, ?_, ?_⟩
  · intro X B Y f m hm
    obtain ⟨_, _, _, square, _, _⟩ := R.pullback_exists f m hm
    exact square.hasPullback
  · intro P X B Y j g f m pb hm
    obtain ⟨I, u, v, chosen, hu, hv⟩ := R.pullback_exists f m hm
    let := chosen.hasPullback
    let : (restrictionMonics (C := C)).RespectsIso := restrictionMonics_respectsIso
    let : R.fullRange.RespectsIso := R.full_respectsIso
    have j_eq : (pb.isoPullback ≪≫ chosen.isoPullback.symm).hom ≫ u = j := by simp
    have g_eq : (pb.isoPullback ≪≫ chosen.isoPullback.symm).hom ≫ v = g := by simp
    constructor
    · rw [← j_eq]
      exact MorphismProperty.RespectsIso.precomp _ _ _ hu
    · intro hf
      rw [← g_eq]
      exact MorphismProperty.RespectsIso.precomp _ _ _ (hv hf)

end CategoricalEssentialIncompleteness.V46.RangeOperation
