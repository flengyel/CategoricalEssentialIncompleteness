/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.RestrictionSpanPullbacks
public import CategoricalEssentialIncompleteness.V46RestrictionSubobjects

/-! # Monic span values under the partial-inverse hypothesis -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.MonicSpanValues

open RestrictionSubobjects
open PartialSpans (Span)

variable {C : Type u} [Category.{v} C] [RestrictionCategory C]

/-- Partial inverses satisfying both inverse equations are unique. -/
theorem partial_inverse_unique {X Y : C} (m : X ⟶ Y) (r s : Y ⟶ X)
    (hmr : m ≫ r = 𝟙 X) (hrm : r ≫ m = rst r)
    (hms : m ≫ s = 𝟙 X) (hsm : s ≫ m = rst s) : r = s := by
  have hrs : r = rst r ≫ s := by
    rw [← hrm, Category.assoc, hms, Category.comp_id]
  have hsr : s = rst s ≫ r := by
    rw [← hsm, Category.assoc, hmr, Category.comp_id]
  have hd : rst r = rst s := by
    have hr := congrArg rst hrs
    have hs := congrArg rst hsr
    rw [rst_comp_rst] at hr hs
    exact hr.trans ((rst_comm r s).trans hs.symm)
  rw [hrs, hd, rst_comp_self]

variable (inverses : MonoInverses C)

theorem inverse_comp {A B D : Tot C} (m : A ⟶ B) (n : B ⟶ D) [Mono m] [Mono n] :
    inverse inverses (m ≫ n) = inverse inverses n ≫ inverse inverses m := by
  apply partial_inverse_unique (m ≫ n).hom _ _
    (hom_inverse inverses _) (inverse_hom inverses _)
  · change (m.hom ≫ n.hom) ≫ (inverse inverses n ≫ inverse inverses m) = _
    rw [Category.assoc, ← Category.assoc n.hom, hom_inverse, Category.id_comp,
      hom_inverse]
  · change (inverse inverses n ≫ inverse inverses m) ≫ (m.hom ≫ n.hom) = _
    calc
      _ = (inverse inverses n ≫ (inverse inverses m ≫ m.hom)) ≫ n.hom := by
        simp only [Category.assoc]
      _ = inverse inverses n ≫ rst (inverse inverses m) ≫ n.hom := by
        rw [inverse_hom]
        simp only [Category.assoc]
      _ = rst (inverse inverses n ≫ inverse inverses m) ≫
          (inverse inverses n ≫ n.hom) := by
        simpa only [Category.assoc] using congrArg (fun k => k ≫ n.hom)
          (rst_comp (inverse inverses n) (inverse inverses m)).symm
      _ = _ := by
        rw [inverse_hom, rst_comm (inverse inverses n ≫ inverse inverses m)
          (inverse inverses n), rst_comp_absorb]

def value {X Y : C} (s : Span X Y) : X ⟶ Y :=
  inverse inverses s.mono ≫ s.map.hom

theorem restrict_value {X Y : C} (s : Span X Y) :
    rst (value inverses s) = rst (inverse inverses s.mono) :=
  rst_comp_of_isTotal _ s.map.property

theorem hom_restrict_inverse {A B : Tot C} (m : A ⟶ B) [Mono m] :
    m.hom ≫ rst (inverse inverses m) = m.hom := by
  rw [← inverse_hom inverses m, ← Category.assoc, hom_inverse, Category.id_comp]

theorem value_eq_of_isomorphic {X Y : C} {s t : Span X Y}
    (h : s.Isomorphic t) : value inverses s = value inverses t := by
  obtain ⟨i, hi, hv⟩ := h
  have hm : s.mono.hom = i.hom.hom ≫ t.mono.hom := congrArg (fun k => k.hom) hi.symm
  have hv' : s.map.hom = i.hom.hom ≫ t.map.hom := congrArg (fun k => k.hom) hv.symm
  have hii : i.inv.hom ≫ i.hom.hom = 𝟙 t.apex.obj :=
    congrArg (fun k => k.hom) i.inv_hom_id
  have hi' : i.hom.hom ≫ i.inv.hom = 𝟙 s.apex.obj :=
    congrArg (fun k => k.hom) i.hom_inv_id
  have he : inverse inverses s.mono = inverse inverses t.mono ≫ i.inv.hom := by
    apply partial_inverse_unique s.mono.hom _ _
      (hom_inverse inverses _) (inverse_hom inverses _)
    · rw [hm, ← Category.assoc, Category.assoc i.hom.hom,
        hom_inverse, Category.comp_id, hi']
    · rw [hm, Category.assoc, ← Category.assoc i.inv.hom, hii, Category.id_comp,
        inverse_hom, rst_comp_of_isTotal _ i.inv.property]
  unfold value
  rw [he, hv', Category.assoc, ← Category.assoc i.inv.hom, hii, Category.id_comp]

theorem isomorphic_of_value_eq {X Y : C} (s t : Span X Y)
    (he : value inverses s = value inverses t) : s.Isomorphic t := by
  have hd : rst (inverse inverses s.mono) = rst (inverse inverses t.mono) := by
    simpa only [restrict_value] using congrArg rst he
  let h := s.mono.hom ≫ inverse inverses t.mono
  let k := t.mono.hom ≫ inverse inverses s.mono
  have hk : h ≫ k = 𝟙 s.apex.obj := by
    dsimp [h, k]
    rw [Category.assoc, ← Category.assoc (inverse inverses t.mono), inverse_hom, ← hd,
      rst_comp_self, hom_inverse]
  have kh : k ≫ h = 𝟙 t.apex.obj := by
    dsimp [h, k]
    rw [Category.assoc, ← Category.assoc (inverse inverses s.mono), inverse_hom, hd,
      rst_comp_self, hom_inverse]
  let h' : s.apex ⟶ t.apex := ⟨h, total_of_comp_total h k (by rw [hk]; exact rst_id _)⟩
  let k' : t.apex ⟶ s.apex := ⟨k, total_of_comp_total k h (by rw [kh]; exact rst_id _)⟩
  refine ⟨⟨h', k', ?_, ?_⟩, ?_, ?_⟩
  · apply WideSubcategory.hom_ext; exact hk
  · apply WideSubcategory.hom_ext; exact kh
  · apply WideSubcategory.hom_ext
    change (s.mono.hom ≫ inverse inverses t.mono) ≫ t.mono.hom = s.mono.hom
    rw [Category.assoc, inverse_hom, ← hd, hom_restrict_inverse]
  · apply WideSubcategory.hom_ext
    change (s.mono.hom ≫ inverse inverses t.mono) ≫ t.map.hom = s.map.hom
    rw [Category.assoc, ← value, ← he]
    change s.mono.hom ≫ (inverse inverses s.mono ≫ s.map.hom) = s.map.hom
    rw [← Category.assoc, hom_inverse, Category.id_comp]

theorem isomorphic_iff_value_eq {X Y : C} (s t : Span X Y) :
    s.Isomorphic t ↔ value inverses s = value inverses t :=
  ⟨value_eq_of_isomorphic inverses, isomorphic_of_value_eq inverses s t⟩

variable [Splits C]

theorem exists_value {X Y : C} (f : X ⟶ Y) :
    ∃ s : Span X Y, value inverses s = f := by
  obtain ⟨A, m, r, hm, hmr, hrm⟩ := Splits.splitting (Idem.ofRestrict f)
  change r ≫ m = rst f at hrm
  have hma : m ≫ rst f = m := by
    rw [← hrm, ← Category.assoc, hmr, Category.id_comp]
  have hmf : isTotal (m ≫ f) := by
    change rst (m ≫ f) = 𝟙 A
    rw [rst_comp_rst_right, hma]
    exact hm
  let m' : (⟨A⟩ : Tot C) ⟶ ⟨X⟩ := ⟨m, hm⟩
  have : Mono m' := by
    constructor
    intro W u v he
    apply WideSubcategory.hom_ext
    have hh := congrArg (fun k => k.hom ≫ r) he
    change (u.hom ≫ m) ≫ r = (v.hom ≫ m) ≫ r at hh
    simpa only [Category.assoc, hmr, Category.comp_id] using hh
  have hri : r ≫ m = rst r := by
    have hh := congrArg rst hrm
    rw [rst_comp_of_isTotal r hm, restrict_restrict] at hh
    exact hrm.trans hh.symm
  have he : inverse inverses m' = r :=
    partial_inverse_unique m _ _ (hom_inverse inverses m') (inverse_hom inverses m') hmr hri
  refine ⟨⟨⟨A⟩, m', ⟨m ≫ f, hmf⟩, inferInstance⟩, ?_⟩
  change inverse inverses m' ≫ (m ≫ f) = f
  rw [he, ← Category.assoc, hrm, rst_comp_self]

theorem inverse_pullback_snd {A B Z : Tot C} (f : A ⟶ Z) (g : B ⟶ Z)
    [Mono g] [HasPullback f g] :
    inverse inverses (pullback.fst f g) ≫ (pullback.snd f g).hom =
      f.hom ≫ inverse inverses g := by
  let p := f.hom ≫ inverse inverses g
  have hcond : rst p ≫ f.hom = p ≫ g.hom := by
    dsimp [p]
    rw [rst_comp, Category.assoc, inverse_hom]
  obtain ⟨h, hf, hs, hr⟩ := PartialSpans.partial_pullback_lift
    (IsPullback.of_hasPullback f g) (rst p) p (restrict_restrict p) hcond
  have hp : (pullback.fst f g).hom ≫ p = (pullback.snd f g).hom := by
    dsimp [p]
    rw [← Category.assoc, ← WideSubcategory.comp_def, pullback.condition,
      WideSubcategory.comp_def, Category.assoc, hom_inverse, Category.comp_id]
  have hright : h ≫ (pullback.fst f g).hom = rst h :=
    hf.trans (hr.trans (restrict_restrict p)).symm
  have hrec : (pullback.fst f g).hom ≫ h ≫ (pullback.fst f g).hom =
      (pullback.fst f g).hom := by
    rw [← Category.assoc, Category.assoc _ h, hf]
    have he := rst_comp (pullback.fst f g).hom p
    rw [hp, show rst (pullback.snd f g).hom = 𝟙 _ from (pullback.snd f g).property,
      Category.id_comp] at he
    exact he.symm
  have hleft : (pullback.fst f g).hom ≫ h = 𝟙 _ := by
    have he := congrArg (fun k => k ≫ inverse inverses (pullback.fst f g)) hrec
    simpa only [Category.assoc, hom_inverse, Category.comp_id] using he
  have hinv := partial_inverse_unique (pullback.fst f g).hom _ _
    (hom_inverse inverses _) (inverse_hom inverses _) hleft hright
  rw [hinv]
  exact hs

theorem value_pullbackComp {X Y Z : C} (s : Span X Y) (t : Span Y Z)
    [HasPullback s.map t.mono] :
    value inverses (s.pullbackComp t) = value inverses s ≫ value inverses t := by
  change inverse inverses (pullback.fst s.map t.mono ≫ s.mono) ≫
    ((pullback.snd s.map t.mono).hom ≫ t.map.hom) = _
  rw [inverse_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (inverse inverses (pullback.fst s.map t.mono)), inverse_pullback_snd]
  simp only [value, Category.assoc]

end CategoricalEssentialIncompleteness.V46.MonicSpanValues
