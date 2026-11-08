/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerTotalCarriers
import PCats.Recursion

/-! # Restriction products of arbitrary uniformly semidecidable carriers -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.Miller.Total
variable {P : Uniform.Family}

def product (X Y : Carrier P) : Carrier P where
  support := {n | (Nat.unpair n).1 ∈ X.support ∧ (Nat.unpair n).2 ∈ Y.support}
  enumerable := (Uniform.Enumerable.comp (Computable.fst.comp Computable.unpair) X.enumerable).and
    (Uniform.Enumerable.comp (Computable.snd.comp Computable.unpair) Y.enumerable)

def totalFromFunction {X Y : Carrier P} (f : ℕ → ℕ) (hf : Computable f)
    (h : ∀ x ∈ X.support,f x ∈ Y.support) : X ⟶ Y :=
  let k : Uniform.N P ⟶ Uniform.N P :=
    Uniform.identityOn (Uniform.N P) X.support X.enumerable ≫ Uniform.totalFromFunction f hf
  arrow k.val k.represented (by
    intro x y hy
    obtain ⟨n,hn,_⟩ := Part.mem_bind_iff.mp hy
    exact ((mem_supportIdentity X.support x n).mp hn).1) (by
    intro x y hy
    obtain ⟨n,hn,hy⟩ := Part.mem_bind_iff.mp hy
    obtain ⟨hx,hnx⟩ := (mem_supportIdentity X.support x n).mp hn
    have hyf : y=f n := Part.mem_some_iff.mp hy
    exact hyf.symm ▸ h n (hnx.symm ▸ hx))

@[simp] theorem mem_totalFromFunction {X Y : Carrier P} (f : ℕ → ℕ) (hf : Computable f)
    (h : ∀ x ∈ X.support,f x ∈ Y.support) (x y : ℕ) :
    y ∈ val (totalFromFunction f hf h) x ↔ x ∈ X.support ∧ y=f x := by
  change y ∈ (supportIdentity X.support x).bind (fun n => Part.some (f n)) ↔ _
  simp only [Part.mem_bind_iff,mem_supportIdentity,Part.mem_some_iff]
  aesop

theorem totalFromFunction_total {X Y : Carrier P} (f : ℕ → ℕ) (hf : Computable f)
    (h : ∀ x ∈ X.support,f x ∈ Y.support) : isTotal (totalFromFunction f hf h) :=
  (total_iff _).mpr (fun x hx => Part.dom_iff_mem.mpr
    ⟨f x,(mem_totalFromFunction f hf h x (f x)).mpr ⟨hx,rfl⟩⟩)

theorem codedPair_represented (f g : ℕ → Part ℕ)
    (hf : Uniform.Represented P .nat .nat f) (hg : Uniform.Represented P .nat .nat g) :
    Uniform.Represented P .nat .nat (fun n => (f n).bind (fun a => (g n).map (Nat.pair a))) := by
  have hc : Computable (fun a : ℕ × ℕ => Nat.pair a.1 a.2) :=
    Primrec₂.natPair.to_comp.comp Computable.fst Computable.snd
  have h := Uniform.Represented.comp (Uniform.Represented.pair hf hg)
    (Uniform.Represented.of_partrec (X := .product .nat .nat) (Y := .nat) hc.partrec)
  exact h.of_eq (fun n => by
    simp only [Part.bind_assoc,Part.bind_map]
    change ((f n).bind fun a => (g n).bind fun b => Part.some (Nat.pair a b)) = _
    simp only [Part.bind_some_eq_map])

def partialFst (X Y : Carrier P) : product X Y ⟶ X :=
  totalFromFunction (fun n => (Nat.unpair n).1) (Computable.fst.comp Computable.unpair)
    (fun _ h => h.1)

def partialSnd (X Y : Carrier P) : product X Y ⟶ Y :=
  totalFromFunction (fun n => (Nat.unpair n).2) (Computable.snd.comp Computable.unpair)
    (fun _ h => h.2)

@[simp] theorem mem_partialFst (X Y : Carrier P) (n m : ℕ) :
    m ∈ val (partialFst X Y) n ↔ n ∈ (product X Y).support ∧ (Nat.unpair n).1 = m := by
  rw [partialFst, mem_totalFromFunction, eq_comm (a := m)]

@[simp] theorem mem_partialSnd (X Y : Carrier P) (n m : ℕ) :
    m ∈ val (partialSnd X Y) n ↔ n ∈ (product X Y).support ∧ (Nat.unpair n).2 = m := by
  rw [partialSnd, mem_totalFromFunction, eq_comm (a := m)]

theorem partialFst_total (X Y : Carrier P) : isTotal (partialFst X Y) :=
  totalFromFunction_total _ _ _

theorem partialSnd_total (X Y : Carrier P) : isTotal (partialSnd X Y) :=
  totalFromFunction_total _ _ _

def partialPair {W X Y : Carrier P} (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ product X Y :=
  arrow (fun n => (val f n).bind fun a => (val g n).map (Nat.pair a))
    (codedPair_represented (val f) (val g) (val_represented f) (val_represented g))
    (by
      intro n m hm
      obtain ⟨a, ha, _⟩ := Part.mem_bind_iff.mp hm
      exact val_source f _ _ ha)
    (by
      intro n m hm
      obtain ⟨a, ha, hm⟩ := Part.mem_bind_iff.mp hm
      obtain ⟨b, hb, rfl⟩ := (Part.mem_map_iff _).mp hm
      exact ⟨by simpa using val_target f _ _ ha, by simpa using val_target g _ _ hb⟩)

theorem mem_restrict {X Y : Carrier P} (f : X ⟶ Y) (n m : ℕ) :
    m ∈ val (rst f) n ↔ (val f n).Dom ∧ m = n := by
  rw [mem_val_restriction, Part.dom_iff_mem]

@[simp] theorem mem_partialPair {W X Y : Carrier P}
    (f : W ⟶ X) (g : W ⟶ Y) (n k : ℕ) :
    k ∈ (val (partialPair f g)) n ↔
      ∃ a ∈ (val f) n, ∃ b ∈ (val g) n, Nat.pair a b = k := by
  simp [partialPair, Part.mem_bind_iff, Part.mem_map_iff]

@[simp] theorem partialPair_fst {W X Y : Carrier P} (f : W ⟶ X) (g : W ⟶ Y) :
    partialPair f g ≫ partialFst X Y = rst g ≫ f := by
  apply val_injective; funext n; apply Part.ext; intro m
  simp only [val_comp, Part.mem_bind_iff, mem_partialPair, mem_partialFst, mem_restrict]
  constructor
  · rintro ⟨k, ⟨a, ha, b, hb, rfl⟩, _, hm⟩
    have ham : a = m := by simpa using hm
    exact ⟨n, ⟨hb.fst, rfl⟩, ham ▸ ha⟩
  · rintro ⟨k, ⟨hg, hkn⟩, hm⟩
    subst k
    let b := ((val g) n).get hg
    have hb : b ∈ (val g) n := Part.get_mem hg
    refine ⟨Nat.pair m b, ⟨m, hm, b, hb, rfl⟩, ?_, by simp⟩
    exact ⟨by simpa using val_target f _ _ hm, by simpa using val_target g _ _ hb⟩

@[simp] theorem partialPair_snd {W X Y : Carrier P} (f : W ⟶ X) (g : W ⟶ Y) :
    partialPair f g ≫ partialSnd X Y = rst f ≫ g := by
  apply val_injective; funext n; apply Part.ext; intro m
  simp only [val_comp, Part.mem_bind_iff, mem_partialPair, mem_partialSnd, mem_restrict]
  constructor
  · rintro ⟨k, ⟨a, ha, b, hb, rfl⟩, _, hm⟩
    have hbm : b = m := by simpa using hm
    exact ⟨n, ⟨ha.fst, rfl⟩, hbm ▸ hb⟩
  · rintro ⟨k, ⟨hf, hkn⟩, hm⟩
    subst k
    let a := ((val f) n).get hf
    have ha : a ∈ (val f) n := Part.get_mem hf
    refine ⟨Nat.pair a m, ⟨a, ha, m, hm, rfl⟩, ?_, by simp⟩
    exact ⟨by simpa using val_target f _ _ ha, by simpa using val_target g _ _ hm⟩

/-- The domain of a pairing is the intersection of the two component domains. -/
theorem rst_partialPair {W X Y : Carrier P} (f : W ⟶ X) (g : W ⟶ Y) :
    rst (partialPair f g) = rst f ≫ rst g := by
  apply val_injective; funext n; apply Part.ext; intro m
  simp only [mem_restrict, Part.dom_iff_mem, mem_partialPair, val_comp, Part.mem_bind_iff]
  constructor
  · rintro ⟨⟨k, a, ha, b, hb, _⟩, hm⟩
    subst m
    exact ⟨n, ⟨⟨a, ha⟩, rfl⟩, ⟨b, hb⟩, rfl⟩
  · rintro ⟨k, ⟨⟨a, ha⟩, hkn⟩, ⟨b, hb⟩, hm⟩
    subst k
    subst m
    exact ⟨⟨Nat.pair a b, a, ha, b, hb, rfl⟩, rfl⟩

/-- Precomposition distributes over partial pairing. -/
theorem comp_partialPair {V W X Y : Carrier P} (h : V ⟶ W) (f : W ⟶ X) (g : W ⟶ Y) :
    h ≫ partialPair f g = partialPair (h ≫ f) (h ≫ g) := by
  apply val_injective; funext n; apply Part.ext; intro m
  simp only [val_comp, Part.mem_bind_iff, mem_partialPair]
  constructor
  · rintro ⟨k, hk, a, ha, b, hb, hm⟩
    exact ⟨a, ⟨k, hk, ha⟩, b, ⟨k, hk, hb⟩, hm⟩
  · rintro ⟨a, ⟨k, hk, ha⟩, b, ⟨l, hl, hb⟩, hm⟩
    have hkl := Part.mem_unique hk hl
    subst l
    exact ⟨k, hk, a, ha, b, hb, hm⟩

/-- An arrow into a numerical product is determined by its two projections. -/
theorem partialPair_proj {W X Y : Carrier P} (h : W ⟶ product X Y) :
    partialPair (h ≫ partialFst X Y) (h ≫ partialSnd X Y) = h := by
  apply val_injective; funext n; apply Part.ext; intro m
  simp only [mem_partialPair, val_comp, Part.mem_bind_iff, mem_partialFst, mem_partialSnd]
  constructor
  · rintro ⟨a, ⟨k, hk, _, rfl⟩, b, ⟨l, hl, _, rfl⟩, hm⟩
    have hkl := Part.mem_unique hk hl
    subst l
    rw [Nat.pair_unpair] at hm
    exact hm ▸ hk
  · intro hm
    exact ⟨(Nat.unpair m).1, ⟨m, hm, val_target h _ _ hm, rfl⟩,
      (Nat.unpair m).2, ⟨m, hm, val_target h _ _ hm, rfl⟩, Nat.pair_unpair m⟩

theorem partial_product_hom_ext {W X Y : Carrier P} {f g : W ⟶ product X Y}
    (hf : f ≫ partialFst X Y = g ≫ partialFst X Y)
    (hg : f ≫ partialSnd X Y = g ≫ partialSnd X Y) : f = g := by
  rw [← partialPair_proj f, hf, hg, partialPair_proj]

def partialProdMap {W X Y Z : Carrier P} (f : W ⟶ X) (g : Y ⟶ Z) :
    product W Y ⟶ product X Z :=
  partialPair (partialFst W Y ≫ f) (partialSnd W Y ≫ g)

def partialDiag (X : Carrier P) : X ⟶ product X X := partialPair (𝟙 X) (𝟙 X)

theorem mem_partialPair_iff {W X Y : Carrier P}
    (f : W ⟶ X) (g : W ⟶ Y) (n m : ℕ) :
    m ∈ (val (partialPair f g)) n ↔
      (Nat.unpair m).1 ∈ (val f) n ∧ (Nat.unpair m).2 ∈ (val g) n := by
  rw [mem_partialPair]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    simpa using And.intro ha hb
  · rintro ⟨ha, hb⟩
    exact ⟨_, ha, _, hb, Nat.pair_unpair m⟩

theorem mem_partialProdMap_iff {W X Y Z : Carrier P}
    (f : W ⟶ X) (g : Y ⟶ Z) (n m : ℕ) :
    m ∈ (val (partialProdMap f g)) n ↔
      (Nat.unpair m).1 ∈ (val f) (Nat.unpair n).1 ∧
      (Nat.unpair m).2 ∈ (val g) (Nat.unpair n).2 := by
  simp only [partialProdMap, mem_partialPair_iff, val_comp, Part.mem_bind_iff,
    mem_partialFst, mem_partialSnd]
  constructor
  · rintro ⟨⟨a, ⟨_, ha⟩, hf⟩, ⟨b, ⟨_, hb⟩, hg⟩⟩
    exact ⟨ha ▸ hf, hb ▸ hg⟩
  · rintro ⟨hf, hg⟩
    have hn : n ∈ (product W Y).support := ⟨val_source f _ _ hf, val_source g _ _ hg⟩
    exact ⟨⟨_, ⟨hn, rfl⟩, hf⟩, ⟨_, ⟨hn, rfl⟩, hg⟩⟩

end CategoricalEssentialIncompleteness.V46.Miller.Total
