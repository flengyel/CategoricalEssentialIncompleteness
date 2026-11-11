/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCategoryJoins

/-! # The actual faithful range inclusion into partial functions

This functor records the underlying partial graph. The fixed-oracle
recursive target is a separate construction, requiring the actual
oracle-machine/relative-recursion comparison.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Uniform
variable (z : Family)
attribute [instance 2000] nativeRestriction

theorem inclusion_i0 (X Y : Object z) :
    (inclusion z).map (i0 X Y) = i0 ((inclusion z).obj X) ((inclusion z).obj Y) := rfl

theorem inclusion_i1 (X Y : Object z) :
    (inclusion z).map (i1 X Y) = i1 ((inclusion z).obj X) ((inclusion z).obj Y) := rfl

theorem comparison_eq_id (X Y : Object z) :
    coproductComparison (inclusion z) X Y =
      𝟙 (coprod ((inclusion z).obj X) ((inclusion z).obj Y)) := by
  rw [coproductComparison,inclusion_i0,inclusion_i1,copair_i0_i1]

def rangeFunctor : RangeFunctor (Object z) PartialFunctions.Pfn where
  toFunctor := inclusion z
  map_restrict _ := rfl
  map_range _ := rfl
  map_zero _ _ := rfl
  comparison_isIso X Y := by
    rw [comparison_eq_id]
    exact (Iso.refl (coprod ((inclusion z).obj X) ((inclusion z).obj Y))).isIso_hom

theorem inclusion_reflects_zero {X Y : Object z} (f : X ⟶ Y)
    (h : (inclusion z).map f = 0) : f = 0 := Arrow.ext h

theorem inclusion_product {W X Y Z : Object z} (f : W ⟶ X) (g : Y ⟶ Z) :
    (inclusion z).map (productMap f g) = PFun.prodMap f.val g.val := by
  apply PFun.ext
  intro p q
  rw [PFun.mem_prodMap]
  exact mem_productMap f g p q

def productComparison (X Y : Object z) :
    (inclusion z).obj (product X Y) ≅
      PartialFun.of (((inclusion z).obj X) × ((inclusion z).obj Y)) := Iso.refl _

theorem inclusion_finiteJoin_graph {X Y : Object z} (L : List (X ⟶ Y))
    (hc : PairwiseCompatible L) (x : carrier z X) (y : carrier z Y) :
    y ∈ (inclusion z).map (finiteJoin L hc) x ↔ ∃ f ∈ L,y ∈ (inclusion z).map f x :=
  finiteJoin_graph L hc x y

theorem inclusion_nonzero : (inclusion z).map (𝟙 (N z)) ≠ 0 := by
  intro h
  have hh := congrArg (fun f : ℕ → Part ℕ => f (0 : ℕ)) h
  change Part.some (0 : ℕ) = Part.none at hh
  have hm := Part.mem_some (0 : ℕ)
  rw [hh] at hm
  exact hm.1

end CategoricalEssentialIncompleteness.V46.Miller.Uniform
