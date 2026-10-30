/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EnumerableProducts

/-! # The restriction product structure on c.e. carriers -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
namespace CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers

attribute [instance 2000] carrierRestriction

theorem partialProdMap_id (X Y : Carrier) :
    partialProdMap (𝟙 X) (𝟙 Y) = 𝟙 (product X Y) := by
  simpa [partialProdMap] using partialPair_proj (𝟙 (product X Y))

theorem partialProdMap_comp {U V W X Y Z : Carrier}
    (f : U ⟶ V) (g : V ⟶ W) (h : X ⟶ Y) (k : Y ⟶ Z) :
    partialProdMap f h ≫ partialProdMap g k = partialProdMap (f ≫ g) (h ≫ k) := by
  apply val_injective; funext n; apply Part.ext; intro m
  simp only [val_comp, Part.mem_bind_iff, mem_partialProdMap_iff]
  constructor
  · rintro ⟨a, ⟨hf, hh⟩, hg, hk⟩
    exact ⟨⟨(Nat.unpair a).1, hf, hg⟩, ⟨(Nat.unpair a).2, hh, hk⟩⟩
  · rintro ⟨⟨a, hf, hg⟩, ⟨b, hh, hk⟩⟩
    exact ⟨Nat.pair a b, by simpa using And.intro hf hh, by simpa using And.intro hg hk⟩

@[simp] theorem partialDiag_fst (X : Carrier) :
    partialDiag X ≫ partialFst X X = 𝟙 X := by
  rw [partialDiag, partialPair_fst]
  exact (Category.comp_id _).trans
    (@RestrictionCategory.rst_id Carrier carrierCategory carrierRestriction X)

@[simp] theorem partialDiag_snd (X : Carrier) :
    partialDiag X ≫ partialSnd X X = 𝟙 X := by
  rw [partialDiag, partialPair_snd]
  exact (Category.comp_id _).trans
    (@RestrictionCategory.rst_id Carrier carrierCategory carrierRestriction X)

theorem partialDiag_partialProdMap {W X Y : Carrier} (f : W ⟶ X) (g : W ⟶ Y) :
    partialDiag W ≫ partialProdMap f g = partialPair f g := by
  rw [partialProdMap, comp_partialPair]
  simp only [← Category.assoc, partialDiag_fst, partialDiag_snd, Category.id_comp]

theorem partialDiag_nat {X Y : Carrier} (f : X ⟶ Y) :
    f ≫ partialDiag Y = partialDiag X ≫ partialProdMap f f := by
  rw [partialDiag_partialProdMap, partialDiag, comp_partialPair]
  simp

instance enumerablePCategoryStruct : PCategoryStruct Carrier where
  nearProd := product
  nearProd_map := partialProdMap
  diag := partialDiag
  p0 := partialFst
  p1 := partialSnd

/-- The derived P-category pairing is the explicit partial numerical pairing. -/
theorem pcategory_partialPairing_eq {W X Y : Carrier} (f : W ⟶ X) (g : W ⟶ Y) :
    PCategoryStruct.partialPairing f g = partialPair f g := partialDiag_partialProdMap f g

/-- The restriction derived from the product structure is the original numerical restriction. -/
theorem pcategory_rst_eq {X Y : Carrier} (f : X ⟶ Y) :
    PCategoryStruct.rst f = rst f := by
  change partialDiag X ≫ partialProdMap (𝟙 X) f ≫ partialFst X Y = rst f
  rw [← Category.assoc, partialDiag_partialProdMap, partialPair_fst, Category.comp_id]

theorem partialProdMap_fst_of_total_right {W X Y Z : Carrier}
    (f : W ⟶ X) (g : Y ⟶ Z) (hg : RestrictionCategory.isTotal g) :
    partialProdMap f g ≫ partialFst X Z = partialFst W Y ≫ f := by
  have ht : rst (partialSnd W Y ≫ g) = 𝟙 _ :=
    RestrictionCategory.isTotal_comp (partialSnd_total W Y) hg
  rw [partialProdMap, partialPair_fst, ht, Category.id_comp]

theorem partialProdMap_snd_of_total_left {W X Y Z : Carrier}
    (f : W ⟶ X) (g : Y ⟶ Z) (hf : RestrictionCategory.isTotal f) :
    partialProdMap f g ≫ partialSnd X Z = partialSnd W Y ≫ g := by
  have ht : rst (partialFst W Y ≫ f) = 𝟙 _ :=
    RestrictionCategory.isTotal_comp (partialFst_total W Y) hf
  rw [partialProdMap, partialPair_snd, ht, Category.id_comp]

theorem pcategory_assoc_eq (X Y Z : Carrier) :
    PCategoryStruct.assoc X Y Z =
      partialPair (partialFst (product X Y) Z ≫ partialFst X Y)
        (partialPair (partialFst (product X Y) Z ≫ partialSnd X Y)
          (partialSnd (product X Y) Z)) := by
  rw [PCategoryStruct.assoc, pcategory_partialPairing_eq, pcategory_partialPairing_eq]
  rfl

theorem mem_pcategory_assoc (X Y Z : Carrier) (n m : ℕ) :
    m ∈ (val (PCategoryStruct.assoc X Y Z)) n ↔
      n ∈ (product (product X Y) Z).support ∧
        m = Nat.pair (Nat.unpair (Nat.unpair n).1).1
          (Nat.pair (Nat.unpair (Nat.unpair n).1).2 (Nat.unpair n).2) := by
  rw [pcategory_assoc_eq]
  simp only [mem_partialPair, val_comp, Part.mem_bind_iff, mem_partialFst, mem_partialSnd]
  simp [product, and_assoc, and_left_comm, and_comm, eq_comm]

theorem mem_pcategory_swap (X Y : Carrier) (n m : ℕ) :
    m ∈ (val (PCategoryStruct.swap X Y)) n ↔
      n ∈ (product X Y).support ∧ m = Nat.pair (Nat.unpair n).2 (Nat.unpair n).1 := by
  rw [PCategoryStruct.swap, pcategory_partialPairing_eq]
  change m ∈ val (partialPair (partialSnd X Y) (partialFst X Y)) n ↔ _
  simp [mem_partialPair, mem_partialFst, mem_partialSnd, and_assoc, eq_comm]

theorem partialProdMap_assoc_nat {X X' Y Y' Z Z' : Carrier}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    partialProdMap (partialProdMap f g) h ≫ PCategoryStruct.assoc X' Y' Z' =
      PCategoryStruct.assoc X Y Z ≫ partialProdMap f (partialProdMap g h) := by
  apply val_injective; funext n; apply Part.ext; intro m
  simp only [val_comp, Part.mem_bind_iff, mem_partialProdMap_iff, mem_pcategory_assoc]
  constructor
  · rintro ⟨k, ⟨⟨hf, hg⟩, hh⟩, _, rfl⟩
    refine ⟨Nat.pair (Nat.unpair (Nat.unpair n).1).1
      (Nat.pair (Nat.unpair (Nat.unpair n).1).2 (Nat.unpair n).2),
      ⟨⟨⟨val_source f _ _ hf, val_source g _ _ hg⟩, val_source h _ _ hh⟩, rfl⟩, ?_⟩
    simpa using And.intro hf (And.intro hg hh)
  · rintro ⟨k, ⟨_, rfl⟩, hf, hg, hh⟩
    simp only [Nat.unpair_pair] at hf hg hh
    refine ⟨Nat.pair (Nat.pair (Nat.unpair m).1 (Nat.unpair (Nat.unpair m).2).1)
      (Nat.unpair (Nat.unpair m).2).2, ?_, ?_, ?_⟩
    · simpa using And.intro (And.intro hf hg) hh
    · simpa [product] using And.intro (And.intro (val_target f _ _ hf) (val_target g _ _ hg)) (val_target h _ _ hh)
    · simp

theorem partialProdMap_swap_nat {X X' Y Y' : Carrier} (f : X ⟶ X') (g : Y ⟶ Y') :
    partialProdMap f g ≫ PCategoryStruct.swap X' Y' =
      PCategoryStruct.swap X Y ≫ partialProdMap g f := by
  apply val_injective; funext n; apply Part.ext; intro m
  simp only [val_comp, Part.mem_bind_iff, mem_partialProdMap_iff, mem_pcategory_swap]
  constructor
  · rintro ⟨k, ⟨hf, hg⟩, _, rfl⟩
    refine ⟨Nat.pair (Nat.unpair n).2 (Nat.unpair n).1,
      ⟨⟨val_source f _ _ hf, val_source g _ _ hg⟩, rfl⟩, ?_⟩
    simpa using And.intro hg hf
  · rintro ⟨k, ⟨_, rfl⟩, hg, hf⟩
    simp only [Nat.unpair_pair] at hf hg
    refine ⟨Nat.pair (Nat.unpair m).2 (Nat.unpair m).1, ?_, ?_, ?_⟩
    · simpa using And.intro hf hg
    · simpa [product] using And.intro (val_target f _ _ hf) (val_target g _ _ hg)
    · simp

instance enumerablePCategory : PCategory Carrier where
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

/-- The two restriction structures agree as structures, including their operation on every arrow. -/
theorem inducedRestriction_eq :
    (PCategory.inducedRestriction : RestrictionCategory Carrier) = carrierRestriction := by
  have h : @RestrictionCategory.rst Carrier carrierCategory PCategory.inducedRestriction =
      @RestrictionCategory.rst Carrier carrierCategory carrierRestriction := by
    funext X Y f
    exact pcategory_rst_eq f
  have hext : ∀ R S : RestrictionCategory Carrier,
      @RestrictionCategory.rst Carrier carrierCategory R =
        @RestrictionCategory.rst Carrier carrierCategory S → R = S := by
    intro R S
    cases R
    cases S
    intro h
    cases h
    rfl
  exact hext _ _ h

theorem partialProdMap_total {W X Y Z : Carrier} (f : W ⟶ X) (g : Y ⟶ Z)
    (hf : isTotal f) (hg : isTotal g) : isTotal (partialProdMap f g) := by
  change rst (partialPair (partialFst W Y ≫ f) (partialSnd W Y ≫ g)) = 𝟙 _
  rw [rst_partialPair, isTotal_comp (partialFst_total _ _) hf,
    isTotal_comp (partialSnd_total _ _) hg, Category.id_comp]

instance enumerableProdominical : RecursionCategory.Prodominical Carrier where
  nearProd_zero_right f := by
    change partialProdMap f 0 = 0
    apply val_injective; funext n; apply Part.ext; intro m
    simp only [mem_partialProdMap_iff, val_zero, Part.notMem_none, and_false]
  nearProd_zero_left f := by
    change partialProdMap 0 f = 0
    apply val_injective; funext n; apply Part.ext; intro m
    simp only [mem_partialProdMap_iff, val_zero, Part.notMem_none, false_and]

end CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers
