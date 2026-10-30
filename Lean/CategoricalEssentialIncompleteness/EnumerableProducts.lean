/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EnumerableCarriers
import PCats.Recursion

/-! # Restriction products of arbitrary c.e. numerical carriers -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers

def product (X Y : Carrier) : Carrier where
  support := {n | (Nat.unpair n).1 ∈ X.support ∧ (Nat.unpair n).2 ∈ Y.support}
  enumerable := (REPred.comp (Computable.fst.comp Computable.unpair) X.enumerable).and
    (REPred.comp (Computable.snd.comp Computable.unpair) Y.enumerable)

def totalFromFunction {X Y : Carrier} (f : ℕ → ℕ) (hf : Computable f)
    (h : ∀ x ∈ X.support, f x ∈ Y.support) : X ⟶ Y :=
  ClassicalPrograms.totalArrow X.enumerable Y.enumerable f hf h

theorem totalFromFunction_total {X Y : Carrier} (f : ℕ → ℕ) (hf : Computable f)
    (h : ∀ x ∈ X.support, f x ∈ Y.support) : isTotal (totalFromFunction f hf h) :=
  ClassicalPrograms.totalArrow_isTotal X.enumerable Y.enumerable f hf h

@[simp] theorem mem_totalFromFunction {X Y : Carrier} (f : ℕ → ℕ) (hf : Computable f)
    (h : ∀ x ∈ X.support, f x ∈ Y.support) (x y : ℕ) :
    y ∈ val (totalFromFunction f hf h) x ↔ x ∈ X.support ∧ y = f x :=
  ClassicalPrograms.mem_restrictedFunction X.support f x y

def partialFst (X Y : Carrier) : product X Y ⟶ X :=
  totalFromFunction (fun n => (Nat.unpair n).1) (Computable.fst.comp Computable.unpair)
    (fun _ h => h.1)

def partialSnd (X Y : Carrier) : product X Y ⟶ Y :=
  totalFromFunction (fun n => (Nat.unpair n).2) (Computable.snd.comp Computable.unpair)
    (fun _ h => h.2)

@[simp] theorem mem_partialFst (X Y : Carrier) (n m : ℕ) :
    m ∈ val (partialFst X Y) n ↔ n ∈ (product X Y).support ∧ (Nat.unpair n).1 = m := by
  rw [partialFst, mem_totalFromFunction, eq_comm (a := m)]

@[simp] theorem mem_partialSnd (X Y : Carrier) (n m : ℕ) :
    m ∈ val (partialSnd X Y) n ↔ n ∈ (product X Y).support ∧ (Nat.unpair n).2 = m := by
  rw [partialSnd, mem_totalFromFunction, eq_comm (a := m)]

theorem partialFst_total (X Y : Carrier) : isTotal (partialFst X Y) :=
  totalFromFunction_total _ _ _

theorem partialSnd_total (X Y : Carrier) : isTotal (partialSnd X Y) :=
  totalFromFunction_total _ _ _

def partialPair {W X Y : Carrier} (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ product X Y :=
  arrow (fun n => (val f n).bind fun a => (val g n).map (Nat.pair a))
    ((val_partrec f).bind
      (((val_partrec g).comp Computable.fst).map
        (Primrec₂.natPair.to_comp.comp
          (Computable.snd.comp Computable.fst) Computable.snd).to₂).to₂)
    (by
      intro n m hm
      obtain ⟨a, ha, _⟩ := Part.mem_bind_iff.mp hm
      exact val_source f _ _ ha)
    (by
      intro n m hm
      obtain ⟨a, ha, hm⟩ := Part.mem_bind_iff.mp hm
      obtain ⟨b, hb, rfl⟩ := (Part.mem_map_iff _).mp hm
      exact ⟨by simpa using val_target f _ _ ha, by simpa using val_target g _ _ hb⟩)

theorem mem_restrict {X Y : Carrier} (f : X ⟶ Y) (n m : ℕ) :
    m ∈ val (rst f) n ↔ (val f n).Dom ∧ m = n := by
  rw [mem_val_restriction, Part.dom_iff_mem]

@[simp] theorem mem_partialPair {W X Y : Carrier}
    (f : W ⟶ X) (g : W ⟶ Y) (n k : ℕ) :
    k ∈ (val (partialPair f g)) n ↔
      ∃ a ∈ (val f) n, ∃ b ∈ (val g) n, Nat.pair a b = k := by
  simp [partialPair, Part.mem_bind_iff, Part.mem_map_iff]

@[simp] theorem partialPair_fst {W X Y : Carrier} (f : W ⟶ X) (g : W ⟶ Y) :
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

@[simp] theorem partialPair_snd {W X Y : Carrier} (f : W ⟶ X) (g : W ⟶ Y) :
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
theorem rst_partialPair {W X Y : Carrier} (f : W ⟶ X) (g : W ⟶ Y) :
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
theorem comp_partialPair {V W X Y : Carrier} (h : V ⟶ W) (f : W ⟶ X) (g : W ⟶ Y) :
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
theorem partialPair_proj {W X Y : Carrier} (h : W ⟶ product X Y) :
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

theorem partial_product_hom_ext {W X Y : Carrier} {f g : W ⟶ product X Y}
    (hf : f ≫ partialFst X Y = g ≫ partialFst X Y)
    (hg : f ≫ partialSnd X Y = g ≫ partialSnd X Y) : f = g := by
  rw [← partialPair_proj f, hf, hg, partialPair_proj]

def partialProdMap {W X Y Z : Carrier} (f : W ⟶ X) (g : Y ⟶ Z) :
    product W Y ⟶ product X Z :=
  partialPair (partialFst W Y ≫ f) (partialSnd W Y ≫ g)

def partialDiag (X : Carrier) : X ⟶ product X X := partialPair (𝟙 X) (𝟙 X)

theorem mem_partialPair_iff {W X Y : Carrier}
    (f : W ⟶ X) (g : W ⟶ Y) (n m : ℕ) :
    m ∈ (val (partialPair f g)) n ↔
      (Nat.unpair m).1 ∈ (val f) n ∧ (Nat.unpair m).2 ∈ (val g) n := by
  rw [mem_partialPair]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    simpa using And.intro ha hb
  · rintro ⟨ha, hb⟩
    exact ⟨_, ha, _, hb, Nat.pair_unpair m⟩

theorem mem_partialProdMap_iff {W X Y Z : Carrier}
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

end CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers
