/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.RestrictionRanges

/-! # Connected alternatives and the local switch -/

universe v u

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (HasZeroMorphisms zero_comp comp_zero)
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts

namespace CategoricalEssentialIncompleteness.LocalConnectedness

variable {C : Type u} [Category.{v} C] [RestrictionCategory C]
variable [HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C]

/-- Connected restriction idempotents admit no nontrivial disjoint binary
decomposition, as in Section 2. -/
def Connected {X : C} (a : Idem X) : Prop :=
  ∀ b c : Idem X, a = b ⊔ c → b ⊓ c = ⊥ → b = ⊥ ∨ c = ⊥

/-- Connected restriction idempotents are jointly epimorphic. -/
class LocallyConnected (C : Type u) [Category.{v} C] [RestrictionCategory C]
    [HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C] : Prop where
  hom_ext : ∀ {X Y : C} (f g : X ⟶ Y),
    (∀ a : Idem X, Connected a → a.hom ≫ f = a.hom ≫ g) → f = g

/-- Every restriction idempotent splits with a total inclusion. -/
class Splits (C : Type u) [Category.{v} C] [RestrictionCategory C] : Prop where
  splitting : ∀ {X : C} (a : Idem X), ∃ (Z : C) (m : Z ⟶ X) (r : X ⟶ Z),
    isTotal m ∧ m ≫ r = 𝟙 Z ∧ r ≫ m = a.hom

omit [HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C] in
theorem Idem.pull_idem {X : C} (a b : Idem X) : Idem.pull a.hom b = a ⊓ b := by
  apply Idem.ext
  change rst (a.hom ≫ b.hom) = a.hom ≫ b.hom
  rw [← a.restriction, rst_comp_rst, b.restriction]

omit [HasZeroMorphisms C] [RestrictionZero C] in
theorem Idem.inf_sup [JoinInverse C] {X : C} (a b c : Idem X) :
    a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) := by
  simpa only [Idem.pull_idem] using JoinInverse.pull_sup a.hom b c

omit [HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C] in
theorem Idem.receives_of_le_pull {X Y : C} (a : Idem X) (f : X ⟶ Y) (b : Idem Y)
    (h : a ≤ Idem.pull f b) : a.hom ≫ f ≫ b.hom = a.hom ≫ f := by
  calc
    _ = a.hom ≫ (Idem.pull f b).hom ≫ f := by rw [Idem.pull_commute]
    _ = _ := by rw [← Category.assoc, Idem.le_def.mp h]

variable [CoprodStruct C] [CategoryTheory.HasCoproducts C] [RestrictionCoproducts C]

/-- Lemma 6.1: a total arrow maps a connected restriction idempotent into
one summand. -/
theorem connected_alternative [JoinInverse C] {X Y Z : C}
    (a : Idem X) (ha : Connected a) (f : X ⟶ coprod Y Z) (hf : isTotal f) :
    a.hom ≫ f ≫ (summand0 Y Z).hom = a.hom ≫ f ∨
    a.hom ≫ f ≫ (summand1 Y Z).hom = a.hom ≫ f := by
  have hc := (summands_complementary Y Z).pull f hf
  have hd : (a ⊓ Idem.pull f (summand0 Y Z)) ⊓
      (a ⊓ Idem.pull f (summand1 Y Z)) = ⊥ := by
    apply le_antisymm _ bot_le
    calc
      _ ≤ Idem.pull f (summand0 Y Z) ⊓ Idem.pull f (summand1 Y Z) :=
        inf_le_inf inf_le_right inf_le_right
      _ = ⊥ := hc.disjoint
  have he : a = (a ⊓ Idem.pull f (summand0 Y Z)) ⊔
      (a ⊓ Idem.pull f (summand1 Y Z)) := by
    rw [← Idem.inf_sup, hc.cover, inf_top_eq]
  rcases ha _ _ he hd with h0 | h1
  · right
    rw [h0, bot_sup_eq] at he
    exact Idem.receives_of_le_pull a f _ (inf_eq_left.mp he.symm)
  · left
    rw [h1, sup_bot_eq] at he
    exact Idem.receives_of_le_pull a f _ (inf_eq_left.mp he.symm)

section SwitchAlgebra

variable {X : C}

omit [HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C] in
theorem switch_restriction (a b : Idem X) :
    rst (copair a.hom b.hom) = (a.sum b).hom := by
  rw [restrict_copair, a.restriction, b.restriction, Idem.sum_hom]

omit [BinaryJoins C] in
theorem switch_branch0 (a b : Idem X) :
    (summand0 X X).hom ≫ (a.sum b).hom =
      (summand0 X X).hom ≫ copair a.hom b.hom ≫ i0 X X := by
  apply hom_ext <;>
    simp only [← Category.assoc, i0_summand0, i1_summand0, Idem.sum_hom,
      i0_coprod_map, i0_copair, zero_comp]

omit [BinaryJoins C] in
theorem switch_branch1 (a b : Idem X) :
    (summand1 X X).hom ≫ (a.sum b).hom =
      (summand1 X X).hom ≫ copair a.hom b.hom ≫ i1 X X := by
  apply hom_ext <;>
    simp only [← Category.assoc, i0_summand1, i1_summand1, Idem.sum_hom,
      i1_coprod_map, i1_copair, zero_comp]

omit [BinaryJoins C] in
theorem switch_first (a b : Idem X) (hab : a ⊓ b = ⊥) :
    copair a.hom b.hom ≫ a.hom = (summand0 X X).hom ≫ copair a.hom b.hom := by
  have hba : b.hom ≫ a.hom = 0 := by
    rw [b.comm a]
    exact congrArg Idem.hom hab
  apply hom_ext <;>
    simp only [← Category.assoc, i0_copair, i1_copair, i0_summand0, i1_summand0,
      a.idem, hba, zero_comp]

omit [BinaryJoins C] in
theorem switch_second (a b : Idem X) (hab : a ⊓ b = ⊥) :
    copair a.hom b.hom ≫ b.hom = (summand1 X X).hom ≫ copair a.hom b.hom := by
  have hab' : a.hom ≫ b.hom = 0 := congrArg Idem.hom hab
  apply hom_ext <;>
    simp only [← Category.assoc, i0_copair, i1_copair, i0_summand1, i1_summand1,
      b.idem, hab', zero_comp]

omit [HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C] [CoprodStruct C]
    [CategoryTheory.HasCoproducts C] [RestrictionCoproducts C] in
theorem comp_eq_of_supported {Y Z : C} (e : Idem X) (u : Y ⟶ X)
    (hu : u ≫ e.hom = u) (k l : X ⟶ Z) (h : e.hom ≫ k = e.hom ≫ l) :
    u ≫ k = u ≫ l := by
  calc
    _ = (u ≫ e.hom) ≫ k := by rw [hu]
    _ = (u ≫ e.hom) ≫ l := by rw [Category.assoc, h, ← Category.assoc]
    _ = _ := by rw [hu]

omit [RestrictionZero C] [BinaryJoins C] [CoprodStruct C]
    [CategoryTheory.HasCoproducts C] [RestrictionCoproducts C] in
theorem comp_zero_of_supported {Y : C} (e d : Idem X) (u : Y ⟶ X)
    (hu : u ≫ e.hom = u) (h : e.hom ≫ d.hom = 0) : u ≫ d.hom = 0 := by
  calc
    _ = (u ≫ e.hom) ≫ d.hom := by rw [hu]
    _ = 0 := by rw [Category.assoc, h, comp_zero]

theorem switch_partial_mono_total [JoinInverse C] [LocallyConnected C]
    (a b : Idem X) (hab : a ⊓ b = ⊥) {Y : C}
    (u v : Y ⟶ coprod X X) (hu : isTotal u) (hv : isTotal v)
    (heq : u ≫ copair a.hom b.hom = v ≫ copair a.hom b.hom) :
    u ≫ (a.sum b).hom = v ≫ (a.sum b).hom := by
  have h01 : (summand0 X X).hom ≫ (summand1 X X).hom = 0 :=
    congrArg Idem.hom (summands_disjoint X X)
  have h10 : (summand1 X X).hom ≫ (summand0 X X).hom = 0 := by
    rw [Idem.comm, h01]
  have branch0 : ∀ {Z : C} (w : Z ⟶ coprod X X),
      w ≫ (summand0 X X).hom = w →
      w ≫ (a.sum b).hom = w ≫ copair a.hom b.hom ≫ i0 X X := by
    intro Z w hw
    exact comp_eq_of_supported _ w hw _ _ (switch_branch0 a b)
  have branch1 : ∀ {Z : C} (w : Z ⟶ coprod X X),
      w ≫ (summand1 X X).hom = w →
      w ≫ (a.sum b).hom = w ≫ copair a.hom b.hom ≫ i1 X X := by
    intro Z w hw
    exact comp_eq_of_supported _ w hw _ _ (switch_branch1 a b)
  apply LocallyConnected.hom_ext
  intro γ hγ
  let x := γ.hom ≫ u
  let y := γ.hom ≫ v
  have heq' : x ≫ copair a.hom b.hom = y ≫ copair a.hom b.hom := by
    simp only [x, y, Category.assoc, heq]
  have hfirst := congrArg (fun k => k ≫ a.hom) heq'
  simp only [Category.assoc, switch_first a b hab] at hfirst
  have hx := connected_alternative γ hγ u hu
  have hy := connected_alternative γ hγ v hv
  simp only [← Category.assoc] at hx hy ⊢
  change x ≫ (summand0 X X).hom = x ∨ x ≫ (summand1 X X).hom = x at hx
  change y ≫ (summand0 X X).hom = y ∨ y ≫ (summand1 X X).hom = y at hy
  change x ≫ (a.sum b).hom = y ≫ (a.sum b).hom
  rcases hx with hx0 | hx1 <;> rcases hy with hy0 | hy1
  · rw [branch0 x hx0, branch0 y hy0]
    simpa only [Category.assoc] using congrArg (fun k => k ≫ i0 X X) heq'
  · have hy0 := comp_zero_of_supported _ _ y hy1 h10
    have hzero : x ≫ copair a.hom b.hom = 0 := by
      simpa only [← Category.assoc, hx0, hy0, zero_comp] using hfirst
    have hzero' : y ≫ copair a.hom b.hom = 0 := heq'.symm.trans hzero
    rw [branch0 x hx0, branch1 y hy1, ← Category.assoc, hzero, zero_comp,
      ← Category.assoc, hzero', zero_comp]
  · have hx0 := comp_zero_of_supported _ _ x hx1 h10
    have hzero : y ≫ copair a.hom b.hom = 0 := by
      simpa only [← Category.assoc, hy0, hx0, zero_comp] using hfirst.symm
    have hzero' : x ≫ copair a.hom b.hom = 0 := heq'.trans hzero
    rw [branch1 x hx1, branch0 y hy0, ← Category.assoc, hzero', zero_comp,
      ← Category.assoc, hzero, zero_comp]
  · rw [branch1 x hx1, branch1 y hy1]
    simpa only [Category.assoc] using congrArg (fun k => k ≫ i1 X X) heq'

end SwitchAlgebra

omit [HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C] [CoprodStruct C]
    [CategoryTheory.HasCoproducts C] [RestrictionCoproducts C] in
theorem partial_mono_of_total_tests [Splits C] {X Y : C} (p : X ⟶ Y)
    (hp : ∀ {W : C} (u v : W ⟶ X), isTotal u → isTotal v →
      u ≫ p = v ≫ p → u ≫ rst p = v ≫ rst p) : PartialMono p := by
  intro W u v heq
  obtain ⟨Z, m, r, hm, hmr, hrm⟩ := Splits.splitting (Idem.ofRestrict (u ≫ p))
  change r ≫ m = rst (u ≫ p) at hrm
  have hmu : isTotal ((m ≫ u) ≫ p) := by
    change rst ((m ≫ u) ≫ p) = 𝟙 Z
    rw [Category.assoc, rst_comp_rst_right]
    have hs : m ≫ rst (u ≫ p) = m := by
      rw [← hrm, ← Category.assoc, hmr, Category.id_comp]
    rw [hs]
    exact hm
  have hmv : isTotal ((m ≫ v) ≫ p) := by
    simpa only [Category.assoc, heq] using hmu
  have he := hp (m ≫ u) (m ≫ v)
    (total_of_comp_total _ p hmu) (total_of_comp_total _ p hmv)
    (by simp only [Category.assoc, heq])
  have hs (w : W ⟶ X) : rst (w ≫ p) ≫ w ≫ rst p = w ≫ rst p := by
    rw [← Category.assoc, rst_comp, Category.assoc, rst_idem]
  calc
    _ = r ≫ ((m ≫ u) ≫ rst p) := by
      simp only [← Category.assoc, hrm]
      simpa only [Category.assoc] using (hs u).symm
    _ = r ≫ ((m ≫ v) ≫ rst p) := by rw [he]
    _ = _ := by
      simp only [← Category.assoc, hrm]
      simpa only [← Category.assoc, heq] using hs v

omit [HasZeroMorphisms C] [RestrictionZero C] [RestrictionCoproducts C] in
theorem range_copair_idem [Ranges C] {X : C} (a b : Idem X) :
    Ranges.range (copair a.hom b.hom) = a ⊔ b := by
  apply le_antisymm
  · apply Ranges.least
    rw [copair_comp, Idem.le_def.mp (le_sup_left : a ≤ a ⊔ b),
      Idem.le_def.mp (le_sup_right : b ≤ a ⊔ b)]
  · apply sup_le
    · have h := Ranges.precomp_le (i0 X X) (copair a.hom b.hom)
      rwa [i0_copair, Ranges.of_idem] at h
    · have h := Ranges.precomp_le (i1 X X) (copair a.hom b.hom)
      rwa [i1_copair, Ranges.of_idem] at h

omit [RestrictionCoproducts C] in
theorem complementary_hom_ext [Ranges C] {X Y : C} {c c' : Idem X}
    (hc : Complementary c c') (f g : X ⟶ Y)
    (h : c.hom ≫ f = c.hom ≫ g) (h' : c'.hom ≫ f = c'.hom ≫ g) : f = g := by
  have he := Ranges.agreement (copair c.hom c'.hom) f g (by
    rw [copair_comp, copair_comp, h, h'])
  rw [range_copair_idem, hc.cover] at he
  simpa only [Idem.top_hom, Category.id_comp] using he

theorem switch_fibers [Ranges C] {X : C} {c c' : Idem X}
    (hc : Complementary c c') (s : X ⟶ coprod X X) (hs : isTotal s)
    (h1 : c.hom ≫ s = c.hom ≫ i1 X X)
    (h0 : c'.hom ≫ s = c'.hom ≫ i0 X X) :
    Idem.pull s (summand0 X X) = c' ∧ Idem.pull s (summand1 X X) = c := by
  have hcc' : c.hom ≫ c'.hom = 0 := congrArg Idem.hom hc.disjoint
  have hc'c : c'.hom ≫ c.hom = 0 := congrArg Idem.hom hc.symm.disjoint
  have he0 : s ≫ (summand0 X X).hom = c'.hom ≫ s := by
    apply complementary_hom_ext hc
    · rw [← Category.assoc, h1, Category.assoc, i1_summand0, comp_zero,
        ← Category.assoc, hcc', zero_comp]
    · rw [← Category.assoc, h0, Category.assoc, i0_summand0,
        ← Category.assoc, c'.idem]
  have he1 : s ≫ (summand1 X X).hom = c.hom ≫ s := by
    apply complementary_hom_ext hc
    · rw [← Category.assoc, h1, Category.assoc, i1_summand1,
        ← Category.assoc, c.idem]
    · rw [← Category.assoc, h0, Category.assoc, i0_summand1, comp_zero,
        ← Category.assoc, hc'c, zero_comp]
  constructor <;> apply Idem.ext
  · rw [Idem.pull_hom, he0, rst_comp_of_isTotal _ hs, c'.restriction]
  · rw [Idem.pull_hom, he1, rst_comp_of_isTotal _ hs, c.restriction]

/-- Proposition 6.2, including partial monicity for arbitrary partial tests
and uniqueness of the section. -/
theorem local_switch [Ranges C] [Splits C] [JoinInverse C] [LocallyConnected C]
    [WeakChoice C] {X : C} (a b : Idem X) (hab : a ⊓ b = ⊥) :
    PartialMono (copair a.hom b.hom) ∧
    ∃! s : X ⟶ coprod X X, SectionOf (copair a.hom b.hom) s ∧
      s ≫ copair a.hom b.hom = (a ⊔ b).hom ∧ rst s = (a ⊔ b).hom := by
  have hp : PartialMono (copair a.hom b.hom) := by
    apply partial_mono_of_total_tests
    intro W u v hu hv heq
    rw [switch_restriction]
    exact switch_partial_mono_total a b hab u v hu hv heq
  obtain ⟨s, hs⟩ := WeakChoice.section_exists _ hp
  have hdom : rst s = (a ⊔ b).hom := by
    have h := hs.domain
    rw [range_copair_idem] at h
    exact congrArg Idem.hom h
  refine ⟨hp, s, ⟨hs, hs.comp.trans hdom, hdom⟩, ?_⟩
  intro t ht
  exact hp.section_unique ht.1 hs

/-- The section of a complementary switch is total and has the two
specified restrictions. -/
theorem complementary_switch [Ranges C] [Splits C] [JoinInverse C]
    [LocallyConnected C] [WeakChoice C] {X : C} (c c' : Idem X)
    (hc : Complementary c c') :
    ∃ s : X ⟶ coprod X X, SectionOf (copair c'.hom c.hom) s ∧ isTotal s ∧
      c.hom ≫ s = c.hom ≫ i1 X X ∧ c'.hom ≫ s = c'.hom ≫ i0 X X := by
  obtain ⟨hp, s, ⟨hs, _, hdom⟩, _⟩ := local_switch c' c hc.symm.disjoint
  have htotal : isTotal s := by rw [hc.symm.cover] at hdom; exact hdom
  have heq : s ≫ copair c'.hom c.hom = 𝟙 X := hs.comp.trans htotal
  have hsc : c.hom ≫ s ≫ rst (copair c'.hom c.hom) = c.hom ≫ s := by
    rw [hs.support]
  have hsc' : c'.hom ≫ s ≫ rst (copair c'.hom c.hom) = c'.hom ≫ s := by
    rw [hs.support]
  have hi1 : c.hom ≫ i1 X X ≫ rst (copair c'.hom c.hom) = c.hom ≫ i1 X X := by
    rw [switch_restriction, Idem.sum_hom, i1_coprod_map, ← Category.assoc, c.idem]
  have hi0 : c'.hom ≫ i0 X X ≫ rst (copair c'.hom c.hom) = c'.hom ≫ i0 X X := by
    rw [switch_restriction, Idem.sum_hom, i0_coprod_map, ← Category.assoc, c'.idem]
  refine ⟨s, hs, htotal, ?_, ?_⟩
  · have h := hp (c.hom ≫ s) (c.hom ≫ i1 X X) (by
      rw [Category.assoc, heq, Category.comp_id, Category.assoc, i1_copair, c.idem])
    simpa only [Category.assoc, hsc, hi1] using h
  · have h := hp (c'.hom ≫ s) (c'.hom ≫ i0 X X) (by
      rw [Category.assoc, heq, Category.comp_id, Category.assoc, i0_copair, c'.idem])
    simpa only [Category.assoc, hsc', hi0] using h

end CategoricalEssentialIncompleteness.LocalConnectedness
