/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalProducts

/-!
# Partial pairing in the numerical category

Partial pairing is defined exactly where both component arrows are defined.
Its projections satisfy the restriction-product equations, and every arrow
into a product is recovered by pairing its two projections.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace CategoricalEssentialIncompleteness
namespace Numerical

def partialFst (X Y : Numerical) : product X Y ⟶ X :=
  (fst (totalObject X) (totalObject Y)).hom

def partialSnd (X Y : Numerical) : product X Y ⟶ Y :=
  (snd (totalObject X) (totalObject Y)).hom

@[simp] theorem mem_partialFst (X Y : Numerical) (n m : ℕ) :
    m ∈ (partialFst X Y).val n ↔ n ∈ (product X Y).carrier ∧ (Nat.unpair n).1 = m := by
  change m ∈ (supportIdentity (product X Y).carrier n).bind
    (fun k ↦ Part.some (Nat.unpair k).1) ↔ _
  simp [Part.mem_bind_iff, eq_comm]

@[simp] theorem mem_partialSnd (X Y : Numerical) (n m : ℕ) :
    m ∈ (partialSnd X Y).val n ↔ n ∈ (product X Y).carrier ∧ (Nat.unpair n).2 = m := by
  change m ∈ (supportIdentity (product X Y).carrier n).bind
    (fun k ↦ Part.some (Nat.unpair k).2) ↔ _
  simp [Part.mem_bind_iff, eq_comm]

theorem partialFst_total (X Y : Numerical) : RestrictionCategory.isTotal (partialFst X Y) :=
  (fst (totalObject X) (totalObject Y)).property

theorem partialSnd_total (X Y : Numerical) : RestrictionCategory.isTotal (partialSnd X Y) :=
  (snd (totalObject X) (totalObject Y)).property

/-- Pair two partial numerical arrows on their common domain. -/
def partialPair {W X Y : Numerical} (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ product X Y where
  val n := (f.val n).bind fun a ↦ (g.val n).map (Nat.pair a)
  computable := f.computable.bind
    ((g.computable.comp Computable.fst).map
      (Primrec₂.natPair.to_comp.comp
        (Computable.snd.comp Computable.fst) Computable.snd).to₂).to₂
  source := by
    intro n m hm
    obtain ⟨a, ha, _⟩ := Part.mem_bind_iff.mp hm
    exact f.source ha
  target := by
    intro n m hm
    obtain ⟨a, ha, hm⟩ := Part.mem_bind_iff.mp hm
    obtain ⟨b, hb, rfl⟩ := (Part.mem_map_iff _).mp hm
    exact ⟨by simpa using f.target ha, by simpa using g.target hb⟩

@[simp] theorem mem_partialPair {W X Y : Numerical}
    (f : W ⟶ X) (g : W ⟶ Y) (n k : ℕ) :
    k ∈ (partialPair f g).val n ↔
      ∃ a ∈ f.val n, ∃ b ∈ g.val n, Nat.pair a b = k := by
  simp [partialPair, Part.mem_bind_iff, Part.mem_map_iff]

@[simp] theorem partialPair_fst {W X Y : Numerical} (f : W ⟶ X) (g : W ⟶ Y) :
    partialPair f g ≫ partialFst X Y = restrict g ≫ f := by
  apply Hom.ext; funext n; apply Part.ext; intro m
  simp only [comp_val, Part.mem_bind_iff, mem_partialPair, mem_partialFst, mem_restrict]
  constructor
  · rintro ⟨k, ⟨a, ha, b, hb, rfl⟩, _, hm⟩
    have ham : a = m := by simpa using hm
    exact ⟨n, ⟨hb.fst, rfl⟩, ham ▸ ha⟩
  · rintro ⟨k, ⟨hg, hkn⟩, hm⟩
    subst k
    let b := (g.val n).get hg
    have hb : b ∈ g.val n := Part.get_mem hg
    refine ⟨Nat.pair m b, ⟨m, hm, b, hb, rfl⟩, ?_, by simp⟩
    exact ⟨by simpa using f.target hm, by simpa using g.target hb⟩

@[simp] theorem partialPair_snd {W X Y : Numerical} (f : W ⟶ X) (g : W ⟶ Y) :
    partialPair f g ≫ partialSnd X Y = restrict f ≫ g := by
  apply Hom.ext; funext n; apply Part.ext; intro m
  simp only [comp_val, Part.mem_bind_iff, mem_partialPair, mem_partialSnd, mem_restrict]
  constructor
  · rintro ⟨k, ⟨a, ha, b, hb, rfl⟩, _, hm⟩
    have hbm : b = m := by simpa using hm
    exact ⟨n, ⟨ha.fst, rfl⟩, hbm ▸ hb⟩
  · rintro ⟨k, ⟨hf, hkn⟩, hm⟩
    subst k
    let a := (f.val n).get hf
    have ha : a ∈ f.val n := Part.get_mem hf
    refine ⟨Nat.pair a m, ⟨a, ha, m, hm, rfl⟩, ?_, by simp⟩
    exact ⟨by simpa using f.target ha, by simpa using g.target hm⟩

/-- The domain of a pairing is the intersection of the two component domains. -/
theorem restrict_partialPair {W X Y : Numerical} (f : W ⟶ X) (g : W ⟶ Y) :
    restrict (partialPair f g) = restrict f ≫ restrict g := by
  apply Hom.ext; funext n; apply Part.ext; intro m
  simp only [mem_restrict, Part.dom_iff_mem, mem_partialPair, comp_val, Part.mem_bind_iff]
  constructor
  · rintro ⟨⟨k, a, ha, b, hb, _⟩, hm⟩
    subst m
    exact ⟨n, ⟨⟨a, ha⟩, rfl⟩, ⟨b, hb⟩, rfl⟩
  · rintro ⟨k, ⟨⟨a, ha⟩, hkn⟩, ⟨b, hb⟩, hm⟩
    subst k
    subst m
    exact ⟨⟨Nat.pair a b, a, ha, b, hb, rfl⟩, rfl⟩

/-- Precomposition distributes over partial pairing. -/
theorem comp_partialPair {V W X Y : Numerical} (h : V ⟶ W) (f : W ⟶ X) (g : W ⟶ Y) :
    h ≫ partialPair f g = partialPair (h ≫ f) (h ≫ g) := by
  apply Hom.ext; funext n; apply Part.ext; intro m
  simp only [comp_val, Part.mem_bind_iff, mem_partialPair]
  constructor
  · rintro ⟨k, hk, a, ha, b, hb, hm⟩
    exact ⟨a, ⟨k, hk, ha⟩, b, ⟨k, hk, hb⟩, hm⟩
  · rintro ⟨a, ⟨k, hk, ha⟩, b, ⟨l, hl, hb⟩, hm⟩
    have hkl := Part.mem_unique hk hl
    subst l
    exact ⟨k, hk, a, ha, b, hb, hm⟩

/-- An arrow into a numerical product is determined by its two projections. -/
theorem partialPair_proj {W X Y : Numerical} (h : W ⟶ product X Y) :
    partialPair (h ≫ partialFst X Y) (h ≫ partialSnd X Y) = h := by
  apply Hom.ext; funext n; apply Part.ext; intro m
  simp only [mem_partialPair, comp_val, Part.mem_bind_iff, mem_partialFst, mem_partialSnd]
  constructor
  · rintro ⟨a, ⟨k, hk, _, rfl⟩, b, ⟨l, hl, _, rfl⟩, hm⟩
    have hkl := Part.mem_unique hk hl
    subst l
    rw [Nat.pair_unpair] at hm
    exact hm ▸ hk
  · intro hm
    exact ⟨(Nat.unpair m).1, ⟨m, hm, h.target hm, rfl⟩,
      (Nat.unpair m).2, ⟨m, hm, h.target hm, rfl⟩, Nat.pair_unpair m⟩

theorem partial_product_hom_ext {W X Y : Numerical} {f g : W ⟶ product X Y}
    (hf : f ≫ partialFst X Y = g ≫ partialFst X Y)
    (hg : f ≫ partialSnd X Y = g ≫ partialSnd X Y) : f = g := by
  rw [← partialPair_proj f, hf, hg, partialPair_proj]

def partialProdMap {W X Y Z : Numerical} (f : W ⟶ X) (g : Y ⟶ Z) :
    product W Y ⟶ product X Z :=
  partialPair (partialFst W Y ≫ f) (partialSnd W Y ≫ g)

def partialDiag (X : Numerical) : X ⟶ product X X := partialPair (𝟙 X) (𝟙 X)

theorem mem_partialPair_iff {W X Y : Numerical}
    (f : W ⟶ X) (g : W ⟶ Y) (n m : ℕ) :
    m ∈ (partialPair f g).val n ↔
      (Nat.unpair m).1 ∈ f.val n ∧ (Nat.unpair m).2 ∈ g.val n := by
  rw [mem_partialPair]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    simpa using And.intro ha hb
  · rintro ⟨ha, hb⟩
    exact ⟨_, ha, _, hb, Nat.pair_unpair m⟩

theorem mem_partialProdMap_iff {W X Y Z : Numerical}
    (f : W ⟶ X) (g : Y ⟶ Z) (n m : ℕ) :
    m ∈ (partialProdMap f g).val n ↔
      (Nat.unpair m).1 ∈ f.val (Nat.unpair n).1 ∧
      (Nat.unpair m).2 ∈ g.val (Nat.unpair n).2 := by
  simp only [partialProdMap, mem_partialPair_iff, comp_val, Part.mem_bind_iff,
    mem_partialFst, mem_partialSnd]
  constructor
  · rintro ⟨⟨a, ⟨_, ha⟩, hf⟩, ⟨b, ⟨_, hb⟩, hg⟩⟩
    exact ⟨ha ▸ hf, hb ▸ hg⟩
  · rintro ⟨hf, hg⟩
    have hn : n ∈ (product W Y).carrier := ⟨f.source hf, g.source hg⟩
    exact ⟨⟨_, ⟨hn, rfl⟩, hf⟩, ⟨_, ⟨hn, rfl⟩, hg⟩⟩

end Numerical
end CategoricalEssentialIncompleteness
