/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.OracleRestrictedCoproducts
import CategoricalEssentialIncompleteness.OracleRestrictedJoins
import CategoricalEssentialIncompleteness.OracleRestrictedCoding

/-! # The faithful, zero-reflecting, product-preserving range inclusion -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted

variable (S : Set ℕ)
attribute [instance 2000] nativeRestriction

theorem inclusion_i0 (X Y : Restricted S) :
    (inclusion S).map (i0 X Y)=i0 ((inclusion S).obj X) ((inclusion S).obj Y) := rfl

theorem inclusion_i1 (X Y : Restricted S) :
    (inclusion S).map (i1 X Y)=i1 ((inclusion S).obj X) ((inclusion S).obj Y) := rfl

theorem comparison_eq_id (X Y : Restricted S) :
    coproductComparison (inclusion S) X Y=𝟙 (coprod ((inclusion S).obj X) ((inclusion S).obj Y)) := by
  rw [coproductComparison,inclusion_i0,inclusion_i1,copair_i0_i1]

def rangeFunctor : RangeFunctor (Restricted S) PartialFunctions.Pfn where
  toFunctor := inclusion S
  map_restrict _ := rfl
  map_range _ := rfl
  map_zero _ _ := rfl
  comparison_isIso X Y := by
    rw [comparison_eq_id]
    exact (Iso.refl (coprod ((inclusion S).obj X) ((inclusion S).obj Y))).isIso_hom

theorem inclusion_reflects_zero {X Y : Restricted S} (f : X ⟶ Y)
    (h : (inclusion S).map f=0) : f=0 := Arrow.ext h

theorem inclusion_product {W X Y Z : Restricted S} (f : W ⟶ X) (g : Y ⟶ Z) :
    (inclusion S).map (productMap f g)=PFun.prodMap f.val g.val := by
  apply PFun.ext
  intro p q
  rw [PFun.mem_prodMap]
  exact mem_productMap f g p q

def productComparison (X Y : Restricted S) :
    (inclusion S).obj (product X Y) ≅
      PartialFun.of (((inclusion S).obj X) × ((inclusion S).obj Y)) := Iso.refl _

theorem inclusion_nonzero : (inclusion S).map (𝟙 (N S))≠0 := by
  intro h
  have hh := congrArg (fun f : ℕ → Part ℕ => f (0 : ℕ)) h
  change Part.some (0 : ℕ)=Part.none at hh
  have hm := Part.mem_some (0 : ℕ)
  rw [hh] at hm
  exact hm.1

end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted
