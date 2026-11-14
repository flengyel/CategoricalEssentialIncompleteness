/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RestrictionProductData
public import CategoricalEssentialIncompleteness.V46AmbientPartialSlice
public import CategoricalEssentialIncompleteness.RestrictionSpanPullbacks

/-! # Binary restriction products of arbitrary total families over T -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.AmbientSliceProducts

open RestrictionSubobjects AmbientPartialSlice

variable {C : Type u} [Category.{v} C] [RestrictionCategory C] [Splits C]

/-- Total pullback projections also jointly detect equality of partial morphisms. -/
theorem partial_pullback_hom_ext {P A B Z : Tot C}
    {fst : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ Z} {g : B ⟶ Z}
    (hp : IsPullback fst snd f g) {W : C} {h k : W ⟶ P.obj}
    (h0 : h ≫ fst.hom = k ≫ fst.hom) (h1 : h ≫ snd.hom = k ≫ snd.hom) : h = k := by
  have hd : rst h = rst k := by
    simpa only [rst_comp_of_isTotal _ fst.property] using congrArg rst h0
  obtain ⟨D, m, r, hm, hmr, hrm⟩ := Splits.splitting (Idem.ofRestrict h)
  change r ≫ m = rst h at hrm
  have hma : m ≫ rst h = m := by
    rw [← hrm, ← Category.assoc, hmr, Category.id_comp]
  have hmh : isTotal (m ≫ h) := by
    change rst (m ≫ h) = 𝟙 D
    rw [rst_comp_rst_right, hma]
    exact hm
  have hmk : isTotal (m ≫ k) := by
    change rst (m ≫ k) = 𝟙 D
    rw [rst_comp_rst_right, ← hd, hma]
    exact hm
  let h' : (⟨D⟩ : Tot C) ⟶ P := ⟨m ≫ h, hmh⟩
  let k' : (⟨D⟩ : Tot C) ⟶ P := ⟨m ≫ k, hmk⟩
  have he : h' = k' := by
    apply hp.hom_ext
    · apply WideSubcategory.hom_ext
      change (m ≫ h) ≫ fst.hom = (m ≫ k) ≫ fst.hom
      simpa only [Category.assoc] using congrArg (fun l => m ≫ l) h0
    · apply WideSubcategory.hom_ext
      change (m ≫ h) ≫ snd.hom = (m ≫ k) ≫ snd.hom
      simpa only [Category.assoc] using congrArg (fun l => m ≫ l) h1
  have he' := congrArg (fun l => r ≫ l.hom) he
  change r ≫ (m ≫ h) = r ≫ (m ≫ k) at he'
  have he'' : rst h ≫ h = rst h ≫ k := by
    simpa only [← Category.assoc, hrm] using he'
  calc
    h = rst h ≫ h := (rst_comp_self h).symm
    _ = rst h ≫ k := he''
    _ = rst k ≫ k := congrArg (fun l => l ≫ k) hd
    _ = k := rst_comp_self k

variable [HasPullbacks (Tot C)] {T : C}

def totalProjection (X : Family T) : (⟨X.base⟩ : Tot C) ⟶ ⟨T⟩ := ⟨X.proj, X.total⟩

def product (X Y : Family T) : Family T where
  base := (pullback (totalProjection X) (totalProjection Y)).obj
  proj := (pullback.fst (totalProjection X) (totalProjection Y)).hom ≫ X.proj
  total := isTotal_comp (pullback.fst (totalProjection X) (totalProjection Y)).property X.total

def first (X Y : Family T) : product X Y ⟶ X :=
  ⟨(pullback.fst (totalProjection X) (totalProjection Y)).hom, by
    change _ = rst (pullback.fst (totalProjection X) (totalProjection Y)).hom ≫ _
    rw [show rst (pullback.fst (totalProjection X) (totalProjection Y)).hom = 𝟙 _ from
      (pullback.fst (totalProjection X) (totalProjection Y)).property, Category.id_comp]
    rfl⟩

def second (X Y : Family T) : product X Y ⟶ Y :=
  ⟨(pullback.snd (totalProjection X) (totalProjection Y)).hom, by
    change _ = rst (pullback.snd (totalProjection X) (totalProjection Y)).hom ≫ _
    rw [show rst (pullback.snd (totalProjection X) (totalProjection Y)).hom = 𝟙 _ from
      (pullback.snd (totalProjection X) (totalProjection Y)).property, Category.id_comp]
    exact congrArg (fun l => l.hom)
      (pullback.condition (f := totalProjection X) (g := totalProjection Y)).symm⟩

omit [Splits C] in
theorem first_total (X Y : Family T) : isTotal (first X Y) :=
  (AmbientPartialSlice.total_iff _).mpr
    (pullback.fst (totalProjection X) (totalProjection Y)).property

omit [Splits C] in
theorem second_total (X Y : Family T) : isTotal (second X Y) :=
  (AmbientPartialSlice.total_iff _).mpr
    (pullback.snd (totalProjection X) (totalProjection Y)).property

theorem exists_pairing {V X Y : Family T} (f : V ⟶ X) (g : V ⟶ Y) :
    ∃ h : V.base ⟶ (product X Y).base,
      h ≫ (first X Y).hom = rst g.hom ≫ f.hom ∧
      h ≫ (second X Y).hom = rst f.hom ≫ g.hom ∧ rst h = rst f.hom ≫ rst g.hom := by
  have hd : rst (rst g.hom ≫ f.hom) = rst (rst f.hom ≫ g.hom) := by
    rw [rst_comp_rst, rst_comp_rst, rst_comm]
  have he : (rst g.hom ≫ f.hom) ≫ X.proj = (rst f.hom ≫ g.hom) ≫ Y.proj := by
    rw [Category.assoc, f.over, Category.assoc, g.over, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun l => l ≫ V.proj) (rst_comm g.hom f.hom)
  obtain ⟨h, h0, h1, hr⟩ := PartialSpans.partial_pullback_lift
    (IsPullback.of_hasPullback (totalProjection X) (totalProjection Y))
      (rst g.hom ≫ f.hom) (rst f.hom ≫ g.hom) hd he
  refine ⟨h, h0, h1, ?_⟩
  exact hr.trans ((rst_comp_rst g.hom f.hom).trans (rst_comm g.hom f.hom))

def pairingLift {V X Y : Family T} (f : V ⟶ X) (g : V ⟶ Y) :
    V.base ⟶ (product X Y).base := (exists_pairing f g).choose

theorem pairingLift_spec {V X Y : Family T} (f : V ⟶ X) (g : V ⟶ Y) :
    pairingLift f g ≫ (first X Y).hom = rst g.hom ≫ f.hom ∧
      pairingLift f g ≫ (second X Y).hom = rst f.hom ≫ g.hom ∧
      rst (pairingLift f g) = rst f.hom ≫ rst g.hom := (exists_pairing f g).choose_spec

def pair {V X Y : Family T} (f : V ⟶ X) (g : V ⟶ Y) : V ⟶ product X Y :=
  ⟨pairingLift f g, by
    change pairingLift f g ≫ ((first X Y).hom ≫ X.proj) = _
    rw [← Category.assoc, (pairingLift_spec f g).1, Category.assoc, f.over,
      (pairingLift_spec f g).2.2, ← Category.assoc]
    exact congrArg (fun l => l ≫ V.proj) (rst_comm g.hom f.hom)⟩

theorem pair_fst {V X Y : Family T} (f : V ⟶ X) (g : V ⟶ Y) :
    pair f g ≫ first X Y = rst g ≫ f := Hom.ext (pairingLift_spec f g).1

theorem pair_snd {V X Y : Family T} (f : V ⟶ X) (g : V ⟶ Y) :
    pair f g ≫ second X Y = rst f ≫ g := Hom.ext (pairingLift_spec f g).2.1

theorem pair_restriction {V X Y : Family T} (f : V ⟶ X) (g : V ⟶ Y) :
    rst (pair f g) = rst f ≫ rst g := Hom.ext (pairingLift_spec f g).2.2

theorem pair_proj {V X Y : Family T} (h : V ⟶ product X Y) :
    pair (h ≫ first X Y) (h ≫ second X Y) = h := by
  dsimp only [product] at h
  apply Hom.ext
  apply partial_pullback_hom_ext
    (IsPullback.of_hasPullback (totalProjection X) (totalProjection Y))
  · have he := congrArg Hom.hom (pair_fst (h ≫ first X Y) (h ≫ second X Y))
    change (pair (h ≫ first X Y) (h ≫ second X Y)).hom ≫
        (pullback.fst (totalProjection X) (totalProjection Y)).hom =
      rst (h.hom ≫ (pullback.snd (totalProjection X) (totalProjection Y)).hom) ≫
        (h.hom ≫ (pullback.fst (totalProjection X) (totalProjection Y)).hom) at he
    rw [rst_comp_of_isTotal _ (pullback.snd (totalProjection X) (totalProjection Y)).property,
      ← Category.assoc, rst_comp_self] at he
    exact he
  · have he := congrArg Hom.hom (pair_snd (h ≫ first X Y) (h ≫ second X Y))
    change (pair (h ≫ first X Y) (h ≫ second X Y)).hom ≫
        (pullback.snd (totalProjection X) (totalProjection Y)).hom =
      rst (h.hom ≫ (pullback.fst (totalProjection X) (totalProjection Y)).hom) ≫
        (h.hom ≫ (pullback.snd (totalProjection X) (totalProjection Y)).hom) at he
    rw [rst_comp_of_isTotal _ (pullback.fst (totalProjection X) (totalProjection Y)).property,
      ← Category.assoc, rst_comp_self] at he
    exact he

def restrictionProducts (T : C) : RestrictionProducts.ProductData (Family T) where
  prod := product
  fst := first
  snd := second
  pair := pair
  fst_total := first_total
  snd_total := second_total
  pair_fst := pair_fst
  pair_snd := pair_snd
  pair_restriction := pair_restriction
  pair_proj := pair_proj

end CategoricalEssentialIncompleteness.V46.AmbientSliceProducts
