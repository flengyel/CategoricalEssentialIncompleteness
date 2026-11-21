/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import PCats.Recursion
public import CategoricalEssentialIncompleteness.NumericalPartialProducts

/-!
# The numerical P-category

Recursive tuple coding supplies the product action, diagonal, and projections.
Their equations make the numerical category a P-category whose induced
restriction is the partial identity on the domain of a partial recursive map.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace CategoricalEssentialIncompleteness
namespace Numerical

attribute [local instance 2000] numericalRestriction

theorem partialProdMap_id (X Y : Numerical) :
    partialProdMap (𝟙 X) (𝟙 Y) = 𝟙 (product X Y) := by
  simpa [partialProdMap] using partialPair_proj (𝟙 (product X Y))

theorem partialProdMap_comp {U V W X Y Z : Numerical}
    (f : U ⟶ V) (g : V ⟶ W) (h : X ⟶ Y) (k : Y ⟶ Z) :
    partialProdMap f h ≫ partialProdMap g k = partialProdMap (f ≫ g) (h ≫ k) := by
  apply Hom.ext; funext n; apply Part.ext; intro m
  simp only [comp_val, Part.mem_bind_iff, mem_partialProdMap_iff]
  constructor
  · rintro ⟨a, ⟨hf, hh⟩, hg, hk⟩
    exact ⟨⟨(Nat.unpair a).1, hf, hg⟩, ⟨(Nat.unpair a).2, hh, hk⟩⟩
  · rintro ⟨⟨a, hf, hg⟩, ⟨b, hh, hk⟩⟩
    exact ⟨Nat.pair a b, by simpa using And.intro hf hh, by simpa using And.intro hg hk⟩

@[simp] theorem partialDiag_fst (X : Numerical) :
    partialDiag X ≫ partialFst X X = 𝟙 X := by
  rw [partialDiag, partialPair_fst]
  exact (Category.comp_id _).trans
    (@RestrictionCategory.rst_id Numerical numericalCategory numericalRestriction X)

@[simp] theorem partialDiag_snd (X : Numerical) :
    partialDiag X ≫ partialSnd X X = 𝟙 X := by
  rw [partialDiag, partialPair_snd]
  exact (Category.comp_id _).trans
    (@RestrictionCategory.rst_id Numerical numericalCategory numericalRestriction X)

theorem partialDiag_partialProdMap {W X Y : Numerical} (f : W ⟶ X) (g : W ⟶ Y) :
    partialDiag W ≫ partialProdMap f g = partialPair f g := by
  rw [partialProdMap, comp_partialPair]
  simp only [← Category.assoc, partialDiag_fst, partialDiag_snd, Category.id_comp]

theorem partialDiag_nat {X Y : Numerical} (f : X ⟶ Y) :
    f ≫ partialDiag Y = partialDiag X ≫ partialProdMap f f := by
  rw [partialDiag_partialProdMap, partialDiag, comp_partialPair]
  simp

instance numericalPCategoryStruct : PCategoryStruct Numerical where
  nearProd := product
  nearProd_map := partialProdMap
  diag := partialDiag
  p0 := partialFst
  p1 := partialSnd

/-- The derived P-category pairing is the explicit partial numerical pairing. -/
theorem pcategory_partialPairing_eq {W X Y : Numerical} (f : W ⟶ X) (g : W ⟶ Y) :
    PCategoryStruct.partialPairing f g = partialPair f g := partialDiag_partialProdMap f g

/-- The restriction derived from the product structure is the original numerical restriction. -/
theorem pcategory_rst_eq {X Y : Numerical} (f : X ⟶ Y) :
    PCategoryStruct.rst f = restrict f := by
  change partialDiag X ≫ partialProdMap (𝟙 X) f ≫ partialFst X Y = restrict f
  rw [← Category.assoc, partialDiag_partialProdMap, partialPair_fst, Category.comp_id]

theorem partialProdMap_fst_of_total_right {W X Y Z : Numerical}
    (f : W ⟶ X) (g : Y ⟶ Z) (hg : RestrictionCategory.isTotal g) :
    partialProdMap f g ≫ partialFst X Z = partialFst W Y ≫ f := by
  have ht : restrict (partialSnd W Y ≫ g) = 𝟙 _ :=
    RestrictionCategory.isTotal_comp (partialSnd_total W Y) hg
  rw [partialProdMap, partialPair_fst, ht, Category.id_comp]

theorem partialProdMap_snd_of_total_left {W X Y Z : Numerical}
    (f : W ⟶ X) (g : Y ⟶ Z) (hf : RestrictionCategory.isTotal f) :
    partialProdMap f g ≫ partialSnd X Z = partialSnd W Y ≫ g := by
  have ht : restrict (partialFst W Y ≫ f) = 𝟙 _ :=
    RestrictionCategory.isTotal_comp (partialFst_total W Y) hf
  rw [partialProdMap, partialPair_snd, ht, Category.id_comp]

theorem pcategory_assoc_eq (X Y Z : Numerical) :
    PCategoryStruct.assoc X Y Z =
      partialPair (partialFst (product X Y) Z ≫ partialFst X Y)
        (partialPair (partialFst (product X Y) Z ≫ partialSnd X Y)
          (partialSnd (product X Y) Z)) := by
  rw [PCategoryStruct.assoc, pcategory_partialPairing_eq, pcategory_partialPairing_eq]
  rfl

theorem mem_pcategory_assoc (X Y Z : Numerical) (n m : ℕ) :
    m ∈ (PCategoryStruct.assoc X Y Z).val n ↔
      n ∈ (product (product X Y) Z).carrier ∧
        m = Nat.pair (Nat.unpair (Nat.unpair n).1).1
          (Nat.pair (Nat.unpair (Nat.unpair n).1).2 (Nat.unpair n).2) := by
  rw [pcategory_assoc_eq]
  simp only [mem_partialPair, comp_val, Part.mem_bind_iff, mem_partialFst, mem_partialSnd]
  simp [product, and_assoc, and_left_comm, and_comm, eq_comm]

theorem mem_pcategory_swap (X Y : Numerical) (n m : ℕ) :
    m ∈ (PCategoryStruct.swap X Y).val n ↔
      n ∈ (product X Y).carrier ∧ m = Nat.pair (Nat.unpair n).2 (Nat.unpair n).1 := by
  rw [PCategoryStruct.swap, pcategory_partialPairing_eq]
  change m ∈ (partialPair (partialSnd X Y) (partialFst X Y)).val n ↔ _
  simp [mem_partialPair, mem_partialFst, mem_partialSnd, and_assoc, eq_comm]

theorem partialProdMap_assoc_nat {X X' Y Y' Z Z' : Numerical}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    partialProdMap (partialProdMap f g) h ≫ PCategoryStruct.assoc X' Y' Z' =
      PCategoryStruct.assoc X Y Z ≫ partialProdMap f (partialProdMap g h) := by
  apply Hom.ext; funext n; apply Part.ext; intro m
  simp only [comp_val, Part.mem_bind_iff, mem_partialProdMap_iff, mem_pcategory_assoc]
  constructor
  · rintro ⟨k, ⟨⟨hf, hg⟩, hh⟩, _, rfl⟩
    refine ⟨Nat.pair (Nat.unpair (Nat.unpair n).1).1
      (Nat.pair (Nat.unpair (Nat.unpair n).1).2 (Nat.unpair n).2),
      ⟨⟨⟨f.source hf, g.source hg⟩, h.source hh⟩, rfl⟩, ?_⟩
    simpa using And.intro hf (And.intro hg hh)
  · rintro ⟨k, ⟨_, rfl⟩, hf, hg, hh⟩
    simp only [Nat.unpair_pair] at hf hg hh
    refine ⟨Nat.pair (Nat.pair (Nat.unpair m).1 (Nat.unpair (Nat.unpair m).2).1)
      (Nat.unpair (Nat.unpair m).2).2, ?_, ?_, ?_⟩
    · simpa using And.intro (And.intro hf hg) hh
    · simpa [product] using And.intro (And.intro (f.target hf) (g.target hg)) (h.target hh)
    · simp

theorem partialProdMap_swap_nat {X X' Y Y' : Numerical} (f : X ⟶ X') (g : Y ⟶ Y') :
    partialProdMap f g ≫ PCategoryStruct.swap X' Y' =
      PCategoryStruct.swap X Y ≫ partialProdMap g f := by
  apply Hom.ext; funext n; apply Part.ext; intro m
  simp only [comp_val, Part.mem_bind_iff, mem_partialProdMap_iff, mem_pcategory_swap]
  constructor
  · rintro ⟨k, ⟨hf, hg⟩, _, rfl⟩
    refine ⟨Nat.pair (Nat.unpair n).2 (Nat.unpair n).1,
      ⟨⟨f.source hf, g.source hg⟩, rfl⟩, ?_⟩
    simpa using And.intro hg hf
  · rintro ⟨k, ⟨_, rfl⟩, hg, hf⟩
    simp only [Nat.unpair_pair] at hf hg
    refine ⟨Nat.pair (Nat.unpair m).2 (Nat.unpair m).1, ?_, ?_, ?_⟩
    · simpa using And.intro hf hg
    · simpa [product] using And.intro (f.target hf) (g.target hg)
    · simp

instance numericalPCategory : PCategory Numerical where
  nearProd_id := partialProdMap_id
  nearProd_comp := partialProdMap_comp
  diag_p0 := partialDiag_fst
  diag_p1 := partialDiag_snd
  diag_p0_p1 X Y := by
    change partialDiag (product X Y) ≫ partialProdMap (partialFst X Y) (partialSnd X Y) =
      𝟙 (product X Y)
    rw [partialDiag_partialProdMap]
    simpa using partialPair_proj (𝟙 (product X Y))
  p0_p0 X Y Z := by
    change partialProdMap (𝟙 X) (partialFst Y Z) ≫ partialFst X Y = partialFst X (product Y Z)
    rw [partialProdMap_fst_of_total_right _ _ (partialFst_total Y Z), Category.comp_id]
  p0_p1 X Y Z := by
    change partialProdMap (𝟙 X) (partialSnd Y Z) ≫ partialFst X Z = partialFst X (product Y Z)
    rw [partialProdMap_fst_of_total_right _ _ (partialSnd_total Y Z), Category.comp_id]
  p1_p0 X Y Z := by
    change partialProdMap (partialFst X Y) (𝟙 Z) ≫ partialSnd X Z = partialSnd (product X Y) Z
    rw [partialProdMap_snd_of_total_left _ _ (partialFst_total X Y), Category.comp_id]
  p1_p1 X Y Z := by
    change partialProdMap (partialSnd X Y) (𝟙 Z) ≫ partialSnd Y Z = partialSnd (product X Y) Z
    rw [partialProdMap_snd_of_total_left _ _ (partialSnd_total X Y), Category.comp_id]
  diag_nat := partialDiag_nat
  p0_nat f := partialProdMap_fst_of_total_right f _ (RestrictionCategory.rst_id _)
  p1_nat f := partialProdMap_snd_of_total_left _ f (RestrictionCategory.rst_id _)
  assoc_nat := partialProdMap_assoc_nat
  swap_nat := partialProdMap_swap_nat

/-- The two restriction structures agree as structures, including their operation on every
morphism. -/
theorem inducedRestriction_eq :
    (PCategory.inducedRestriction : RestrictionCategory Numerical) = numericalRestriction := by
  have h : @RestrictionCategory.rst Numerical numericalCategory PCategory.inducedRestriction =
      @RestrictionCategory.rst Numerical numericalCategory numericalRestriction := by
    funext X Y f
    exact pcategory_rst_eq f
  have hext : ∀ R S : RestrictionCategory Numerical,
      @RestrictionCategory.rst Numerical numericalCategory R =
        @RestrictionCategory.rst Numerical numericalCategory S → R = S := by
    intro R S
    cases R
    cases S
    intro h
    cases h
    rfl
  exact hext _ _ h

instance numericalProdominical : RecursionCategory.Prodominical Numerical where
  nearProd_zero_right f := by
    change partialProdMap f 0 = 0
    apply Hom.ext; funext n; apply Part.ext; intro m
    simp only [mem_partialProdMap_iff, zero_val, Part.notMem_none, and_false]
  nearProd_zero_left f := by
    change partialProdMap 0 f = 0
    apply Hom.ext; funext n; apply Part.ext; intro m
    simp only [mem_partialProdMap_iff, zero_val, Part.notMem_none, false_and]

end Numerical
end CategoricalEssentialIncompleteness
