/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerTotalProducts

/-! # Tagged coproducts of arbitrary uniformly semidecidable carriers -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total
variable {P : Uniform.Family}
theorem case_represented (f g : ℕ → Part ℕ)
    (hf : Uniform.Represented P .nat .nat f) (hg : Uniform.Represented P .nat .nat g) :
    Uniform.Represented P .nat .nat (fun n : ℕ => if n%2=0 then f (n/2) else g (n/2)) := by
  have h0 : REPred (fun a : ℕ × ℕ => a.1%2=0) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.fst (.const 2)) (.const 0)).computablePred.to_re
  have h1 : REPred (fun a : ℕ × ℕ => a.1%2=1) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.fst (.const 2)) (.const 1)).computablePred.to_re
  have hd : Computable (fun a : ℕ × ℕ => (a.1/2,a.2)) :=
    Computable.pair (Primrec.nat_div.to_comp.comp Computable.fst (.const 2)) Computable.snd
  have ef := Uniform.Enumerable.comp hd
    ((Uniform.represented_iff_graph_enumerable P .nat .nat f).mp hf)
  have eg := Uniform.Enumerable.comp hd
    ((Uniform.represented_iff_graph_enumerable P .nat .nat g).mp hg)
  apply (Uniform.represented_iff_graph_enumerable P .nat .nat _).mpr
  exact (((Uniform.Enumerable.of_re h0).and ef).or ((Uniform.Enumerable.of_re h1).and eg)).of_eq
    (fun a => by
      rcases a with ⟨n,m⟩
      change ((n%2=0 ∧ m ∈ f (n/2)) ∨ (n%2=1 ∧ m ∈ g (n/2))) ↔ _
      by_cases he : n%2=0
      · simp [he]
      · have ho : n%2=1 := by omega
        simp [ho])


def coproduct (X Y : (Carrier P)) : (Carrier P) where
  support := {n | (n % 2 = 0 ∧ n / 2 ∈ X.support) ∨ (n % 2 = 1 ∧ n / 2 ∈ Y.support)}
  enumerable := by
    have hd : Computable (fun n : ℕ => n / 2) := Primrec.nat_div.to_comp.comp .id (.const 2)
    have hm : Primrec (fun n : ℕ => n % 2) := Primrec.nat_mod.comp .id (.const 2)
    exact ((Uniform.Enumerable.of_re ((Primrec.eq.comp hm (.const 0)).computablePred.to_re)).and
      (Uniform.Enumerable.comp hd X.enumerable)).or
      ((Uniform.Enumerable.of_re ((Primrec.eq.comp hm (.const 1)).computablePred.to_re)).and
        (Uniform.Enumerable.comp hd Y.enumerable))

@[simp] theorem mem_coproduct_even (X Y : (Carrier P)) (n : ℕ) :
    2*n ∈ (coproduct X Y).support ↔ n ∈ X.support := by simp [coproduct]

@[simp] theorem mem_coproduct_odd (X Y : (Carrier P)) (n : ℕ) :
    2*n+1 ∈ (coproduct X Y).support ↔ n ∈ Y.support := by
  simp [coproduct, Nat.add_div, Nat.add_mod]

def inl (X Y : (Carrier P)) : X ⟶ coproduct X Y :=
  totalFromFunction (fun n => 2*n) (Primrec.nat_mul.to_comp.comp (.const 2) .id)
    (fun n hn => (mem_coproduct_even X Y n).mpr hn)

def inr (X Y : (Carrier P)) : Y ⟶ coproduct X Y :=
  totalFromFunction (fun n => 2*n+1)
    (Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (.const 2) .id) (.const 1))
    (fun n hn => (mem_coproduct_odd X Y n).mpr hn)

def copairRaw {X Y Z : (Carrier P)} (f : X ⟶ Z) (g : Y ⟶ Z) : coproduct X Y ⟶ Z :=
  arrow (fun n => if n % 2 = 0 then val f (n/2) else val g (n/2))
    (case_represented (val f) (val g) (val_represented f) (val_represented g))
    (by
      intro n m h
      by_cases he : n % 2 = 0
      · exact Or.inl ⟨he, val_source f _ _ (by simpa [he] using h)⟩
      · exact Or.inr ⟨by omega, val_source g _ _ (by simpa [he] using h)⟩)
    (by
      intro n m h
      by_cases he : n % 2 = 0
      · exact val_target f _ _ (by simpa [he] using h)
      · exact val_target g _ _ (by simpa [he] using h))

@[simp] theorem val_copair_even {X Y Z : (Carrier P)} (f : X ⟶ Z) (g : Y ⟶ Z) (n : ℕ) :
    val (copairRaw f g) (2*n) = val f n := by
  change (if (2*n)%2=0 then val f ((2*n)/2) else val g ((2*n)/2)) = _
  simp

@[simp] theorem val_copair_odd {X Y Z : (Carrier P)} (f : X ⟶ Z) (g : Y ⟶ Z) (n : ℕ) :
    val (copairRaw f g) (2*n+1) = val g n := by
  change (if (2*n+1)%2=0 then val f ((2*n+1)/2) else val g ((2*n+1)/2)) = _
  simp [Nat.add_div, Nat.add_mod]

theorem val_inl_at (X Y : (Carrier P)) (n : ℕ) (hn : n ∈ X.support) :
    val (inl X Y) n = Part.some (2*n) :=
  Part.eq_some_iff.mpr ((mem_totalFromFunction _ _ _ _ _).mpr ⟨hn, rfl⟩)

theorem val_inr_at (X Y : (Carrier P)) (n : ℕ) (hn : n ∈ Y.support) :
    val (inr X Y) n = Part.some (2*n+1) :=
  Part.eq_some_iff.mpr ((mem_totalFromFunction _ _ _ _ _).mpr ⟨hn, rfl⟩)

@[simp] theorem inl_copairRaw {X Y Z : (Carrier P)} (f : X ⟶ Z) (g : Y ⟶ Z) :
    inl X Y ≫ copairRaw f g = f := by
  apply val_ext_on_source
  intro n hn
  rw [val_comp, val_inl_at _ _ _ hn, Part.bind_some, val_copair_even]

@[simp] theorem inr_copairRaw {X Y Z : (Carrier P)} (f : X ⟶ Z) (g : Y ⟶ Z) :
    inr X Y ≫ copairRaw f g = g := by
  apply val_ext_on_source
  intro n hn
  rw [val_comp, val_inr_at _ _ _ hn, Part.bind_some, val_copair_odd]

theorem coproduct_hom_ext {X Y Z : (Carrier P)} {f g : coproduct X Y ⟶ Z}
    (hl : inl X Y ≫ f = inl X Y ≫ g) (hr : inr X Y ≫ f = inr X Y ≫ g) : f = g := by
  apply val_ext_on_source
  intro n hn
  rcases hn with ⟨he, hx⟩ | ⟨he, hy⟩
  · have hv := congrArg (fun k => val k (n/2)) hl
    rw [val_comp, val_comp, val_inl_at _ _ _ hx, Part.bind_some, Part.bind_some] at hv
    have hn : 2*(n/2)=n := by omega
    rwa [hn] at hv
  · have hv := congrArg (fun k => val k (n/2)) hr
    rw [val_comp, val_comp, val_inr_at _ _ _ hy, Part.bind_some, Part.bind_some] at hv
    have hn : 2*(n/2)+1=n := by omega
    rwa [hn] at hv

@[simp] theorem copairRaw_comp {X Y Z W : (Carrier P)} (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ W) :
    copairRaw f g ≫ h = copairRaw (f ≫ h) (g ≫ h) := by
  apply coproduct_hom_ext <;> simp [← Category.assoc]

instance : CoprodStruct (Carrier P) where
  coprod := coproduct
  coprod_map f g := copairRaw (f ≫ inl _ _) (g ≫ inr _ _)
  codiag X := copairRaw (𝟙 X) (𝟙 X)
  i0 := inl
  i1 := inr

open CoprodStruct

@[simp] theorem coprod_eq (X Y : (Carrier P)) : coprod X Y = coproduct X Y := rfl
@[simp] theorem i0_eq (X Y : (Carrier P)) : i0 X Y = inl X Y := rfl
@[simp] theorem i1_eq (X Y : (Carrier P)) : i1 X Y = inr X Y := rfl
@[simp] theorem codiag_eq (X : (Carrier P)) : codiag X = copairRaw (𝟙 X) (𝟙 X) := rfl

@[simp, reassoc] theorem inl_map {W X Y Z : (Carrier P)} (f : W ⟶ X) (g : Y ⟶ Z) :
    inl W Y ≫ coprod_map f g = f ≫ inl X Z := inl_copairRaw _ _

@[simp, reassoc] theorem inr_map {W X Y Z : (Carrier P)} (f : W ⟶ X) (g : Y ⟶ Z) :
    inr W Y ≫ coprod_map f g = g ≫ inr X Z := inr_copairRaw _ _

instance : CategoryTheory.HasCoproducts (Carrier P) where
  coprod_id X Y := by apply coproduct_hom_ext <;> simp
  coprod_comp f g h k := by
    apply coproduct_hom_ext <;> simp [Category.assoc, inl_map_assoc, inr_map_assoc]
  i0_codiag X := inl_copairRaw _ _
  i1_codiag X := inr_copairRaw _ _
  i0_i1_codiag X Y := by
    apply coproduct_hom_ext <;> simp [inl_map_assoc, inr_map_assoc]
  codiag_nat f := by
    apply coproduct_hom_ext <;> simp [inl_map_assoc, inr_map_assoc]
  i0_nat f := by simp
  i0_nat_right g := by simp
  i1_nat f := by simp
  i1_nat_left f := by simp

instance : RestrictionCoproducts (Carrier P) where
  total_i0 X Y := totalFromFunction_total (fun n => 2*n)
    (Primrec.nat_mul.to_comp.comp (.const 2) .id)
    (fun n hn => (mem_coproduct_even X Y n).mpr hn)
  total_i1 X Y := totalFromFunction_total (fun n => 2*n+1)
    (Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (.const 2) .id) (.const 1))
    (fun n hn => (mem_coproduct_odd X Y n).mpr hn)

theorem val_post_inl {W X Y : (Carrier P)} (f : W ⟶ X) (n : ℕ) :
    val (f ≫ inl X Y) n = (val f n).map (fun k => 2*k) := by
  apply Part.ext
  intro m
  simp only [mem_val_comp, inl, mem_totalFromFunction, Part.mem_map_iff]
  constructor
  · rintro ⟨k, hk, _, he⟩
    exact ⟨k, hk, he.symm⟩
  · rintro ⟨k, hk, he⟩
    exact ⟨k, hk, val_target f n k hk, he.symm⟩

theorem val_post_inr {W X Y : (Carrier P)} (f : W ⟶ Y) (n : ℕ) :
    val (f ≫ inr X Y) n = (val f n).map (fun k => 2*k+1) := by
  apply Part.ext
  intro m
  simp only [mem_val_comp, inr, mem_totalFromFunction, Part.mem_map_iff]
  constructor
  · rintro ⟨k, hk, _, he⟩
    exact ⟨k, hk, he.symm⟩
  · rintro ⟨k, hk, he⟩
    exact ⟨k, hk, val_target f n k hk, he.symm⟩

@[simp] theorem val_map_even {W X Y Z : (Carrier P)} (f : W ⟶ X) (g : Y ⟶ Z) (n : ℕ) :
    val (coprod_map f g) (2*n) = (val f n).map (fun k => 2*k) := by
  change val (copairRaw (f ≫ inl X Z) (g ≫ inr X Z)) (2*n) = _
  rw [val_copair_even, val_post_inl]

@[simp] theorem val_map_odd {W X Y Z : (Carrier P)} (f : W ⟶ X) (g : Y ⟶ Z) (n : ℕ) :
    val (coprod_map f g) (2*n+1) = (val g n).map (fun k => 2*k+1) := by
  change val (copairRaw (f ≫ inl X Z) (g ≫ inr X Z)) (2*n+1) = _
  rw [val_copair_odd, val_post_inr]

theorem coproductMap_total {W X Y Z : (Carrier P)} (f : W ⟶ X) (g : Y ⟶ Z)
    (hf : isTotal f) (hg : isTotal g) : isTotal (coprod_map f g) := by
  apply (total_iff _).mpr
  intro n hn
  rcases hn with ⟨he, hx⟩ | ⟨he, hy⟩
  · have hn : n=2*(n/2) := by omega
    rw [hn, val_map_even]
    exact (total_iff f).mp hf _ hx
  · have hn : n=2*(n/2)+1 := by omega
    rw [hn, val_map_odd]
    exact (total_iff g).mp hg _ hy

end CategoricalEssentialIncompleteness.V46.Miller.Total
