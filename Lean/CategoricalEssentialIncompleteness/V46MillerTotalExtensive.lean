/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerTotalUnderlyingPullbacks
public import CategoricalEssentialIncompleteness.V46MillerTotalFiniteCoproducts
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-! # Uniform semidecidable-carrier total splitting: Extensive -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total
variable {P : Uniform.Family}

theorem underlying_inl_val (X Y : (TotalCategory P)) (x : {n // n ∈ X.obj.support}) :
    (underlying.map (totalInl X Y) x).val=2*x.val :=
  Part.mem_unique (totalFunction_mem (totalInl X Y) x)
    (Part.eq_some_iff.mp (val_inl_at X.obj Y.obj x.val x.property))

theorem underlying_inr_val (X Y : (TotalCategory P)) (x : {n // n ∈ Y.obj.support}) :
    (underlying.map (totalInr X Y) x).val=2*x.val+1 :=
  Part.mem_unique (totalFunction_mem (totalInr X Y) x)
    (Part.eq_some_iff.mp (val_inr_at X.obj Y.obj x.val x.property))

def underlyingCoproduct_isColimit (X Y : (TotalCategory P)) :
    IsColimit (BinaryCofan.mk (underlying.map (totalInl X Y)) (underlying.map (totalInr X Y))) := by
  apply Classical.choice
  apply (Types.binaryCofan_isColimit_iff _).mpr
  refine ⟨?_,?_,isCompl_iff.mpr ⟨?_,?_⟩⟩
  · intro x y h
    apply Subtype.ext
    have he := congrArg Subtype.val h
    change (underlying.map (totalInl X Y) x).val=(underlying.map (totalInl X Y) y).val at he
    simp only [underlying_inl_val] at he
    omega
  · intro x y h
    apply Subtype.ext
    have he := congrArg Subtype.val h
    change (underlying.map (totalInr X Y) x).val=(underlying.map (totalInr X Y) y).val at he
    simp only [underlying_inr_val] at he
    omega
  · apply Set.disjoint_left.mpr
    rintro z ⟨x,hx⟩ ⟨y,hy⟩
    have he := congrArg Subtype.val (hx.trans hy.symm)
    change (underlying.map (totalInl X Y) x).val=(underlying.map (totalInr X Y) y).val at he
    simp only [underlying_inl_val,underlying_inr_val] at he
    omega
  · apply codisjoint_iff.mpr
    apply Set.eq_univ_of_forall
    intro z
    change z ∈ Set.range (underlying.map (totalInl X Y)) ∨
      z ∈ Set.range (underlying.map (totalInr X Y))
    rcases z.property with ⟨he,hs⟩ | ⟨he,hs⟩
    · refine Or.inl ⟨⟨z.val/2,hs⟩,?_⟩
      apply Subtype.ext
      rw [underlying_inl_val]
      change 2*(z.val/2)=z.val
      omega
    · refine Or.inr ⟨⟨z.val/2,hs⟩,?_⟩
      apply Subtype.ext
      rw [underlying_inr_val]
      change 2*(z.val/2)+1=z.val
      omega

instance underlying_preservesPair (X Y : (TotalCategory P)) : PreservesColimit (Limits.pair X Y) underlying :=
  preservesColimit_of_preserves_colimit_cocone (coproductIsColimit X Y)
    ((isColimitMapCoconeBinaryCofanEquiv underlying (totalInl X Y) (totalInr X Y)).symm
      (underlyingCoproduct_isColimit X Y))

instance underlying_preservesBinaryCoproducts :
    PreservesColimitsOfShape (Discrete WalkingPair) (underlying (P := P)) where
  preservesColimit := by
    intro K
    exact preservesColimit_of_iso_diagram underlying (diagramIsoPair K).symm

instance totalFinitaryExtensive : FinitaryExtensive (TotalCategory P) :=
  finitaryExtensive_of_preserves_and_reflects_isomorphism underlying

instance underlying_initialEmpty : IsEmpty ((underlying (P := P)).obj (⊥_ (TotalCategory P))) where
  false x := ((underlying (P := P)).map (initial.to (⟨emptyCarrier⟩ : TotalCategory P)) x).property

def underlying_initialIsInitial : IsInitial ((underlying (P := P)).obj (⊥_ (TotalCategory P))) :=
  ((Types.initial_iff_empty _).mpr underlying_initialEmpty).some

instance underlying_preservesInitial : PreservesColimit (Functor.empty.{0} (TotalCategory P)) underlying :=
  preservesInitial_of_iso underlying
    (CategoryTheory.Limits.initialIsInitial.uniqueUpToIso underlying_initialIsInitial)

instance underlying_preservesEmpty : PreservesColimitsOfShape (Discrete PEmpty.{1}) (underlying (P := P)) :=
  preservesColimitsOfShape_pempty_of_preservesInitial underlying

instance underlying_preservesFiniteCoproducts (J : Type*) [Finite J] :
    PreservesColimitsOfShape (Discrete J) (underlying (P := P)) :=
  PreservesFiniteCoproducts.of_preserves_binary_and_initial underlying J

end CategoricalEssentialIncompleteness.V46.Miller.Total
