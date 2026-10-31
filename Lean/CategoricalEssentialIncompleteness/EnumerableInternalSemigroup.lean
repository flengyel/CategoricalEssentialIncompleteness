/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EnumerableFreeSemigroup

/-! # Internal associative multiplication induces the component semigroup -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers

def elementPair {M : Carrier} (a b : Element M) : Element (product M M) :=
  ⟨Nat.pair a.val b.val,by
    change (Nat.unpair (Nat.pair a.val b.val)).1 ∈ M.support ∧
      (Nat.unpair (Nat.pair a.val b.val)).2 ∈ M.support
    simpa only [Nat.unpair_pair] using And.intro a.property b.property⟩

def multiplyValue {M : Carrier} (mu : product M M ⟶ M) (ht : isTotal mu)
    (a b : Element M) : Element M := typedMap mu ht (elementPair a b)

theorem multiplyValue_mem {M : Carrier} (mu : product M M ⟶ M) (ht : isTotal mu)
    (a b : Element M) : (multiplyValue mu ht a b).val ∈ val mu (Nat.pair a.val b.val) :=
  typedMap_mem mu ht (elementPair a b)

theorem multiplyValue_assoc {M : Carrier} (mu : product M M ⟶ M) (ht : isTotal mu)
    (ha : partialProdMap mu (𝟙 M) ≫ mu=
      PCategoryStruct.assoc M M M ≫ partialProdMap (𝟙 M) mu ≫ mu)
    (a b c : Element M) :
    multiplyValue mu ht (multiplyValue mu ht a b) c=
      multiplyValue mu ht a (multiplyValue mu ht b c) := by
  let ab := multiplyValue mu ht a b
  let bc := multiplyValue mu ht b c
  let n := Nat.pair (Nat.pair a.val b.val) c.val
  have hl : (multiplyValue mu ht ab c).val ∈ val (partialProdMap mu (𝟙 M) ≫ mu) n := by
    apply (mem_val_comp _ _ _ _).mpr
    refine ⟨Nat.pair ab.val c.val,?_,multiplyValue_mem mu ht ab c⟩
    apply (mem_partialProdMap_iff _ _ _ _).mpr
    simp only [n,Nat.unpair_pair]
    exact ⟨multiplyValue_mem mu ht a b,
      (mem_supportIdentity M.support c.val c.val).mpr ⟨c.property,rfl⟩⟩
  have hr : (multiplyValue mu ht a bc).val ∈
      val (PCategoryStruct.assoc M M M ≫ partialProdMap (𝟙 M) mu ≫ mu) n := by
    apply (mem_val_comp _ _ _ _).mpr
    refine ⟨Nat.pair a.val (Nat.pair b.val c.val),?_,?_⟩
    · apply (mem_pcategory_assoc _ _ _ _ _).mpr
      constructor
      · change (Nat.unpair n).1 ∈ (product M M).support ∧ (Nat.unpair n).2 ∈ M.support
        simp only [n,Nat.unpair_pair]
        exact ⟨(elementPair a b).property,c.property⟩
      · simp only [n,Nat.unpair_pair]
    · apply (mem_val_comp _ _ _ _).mpr
      refine ⟨Nat.pair a.val bc.val,?_,multiplyValue_mem mu ht a bc⟩
      apply (mem_partialProdMap_iff _ _ _ _).mpr
      simp only [Nat.unpair_pair]
      exact ⟨(mem_supportIdentity M.support a.val a.val).mpr ⟨a.property,rfl⟩,
        multiplyValue_mem mu ht b c⟩
  rw [ha] at hl
  exact Subtype.ext (Part.mem_unique hl hr)

def semigroupOfMultiplication {M : Carrier} (mu : product M M ⟶ M) (ht : isTotal mu)
    (ha : partialProdMap mu (𝟙 M) ≫ mu=
      PCategoryStruct.assoc M M M ≫ partialProdMap (𝟙 M) mu ≫ mu) : Semigroup (Element M) where
  mul := multiplyValue mu ht
  mul_assoc := multiplyValue_assoc mu ht ha

end CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers
