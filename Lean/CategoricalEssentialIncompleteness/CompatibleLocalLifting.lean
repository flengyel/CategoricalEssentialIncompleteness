/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.LocalLifting

/-! # Local lifting with a proved comparison of restriction structures -/

@[expose] public section

universe u v u' v'
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.PCategoryStruct (nearProd diag)
open CategoryTheory.CoprodStruct (coprod)

namespace CategoricalEssentialIncompleteness.LocalConnectedness

variable {R : Type u} {A : Type u'} [Category.{v} R] [Category.{v'} A]
variable [PCategoryStruct R] [PCategory R] [native : RestrictionCategory R]
variable [RestrictionCategory A]
variable [CategoryTheory.Limits.HasZeroMorphisms R] [RestrictionZero R] [BinaryJoins R]
variable [CategoryTheory.Limits.HasZeroMorphisms A] [RestrictionZero A] [BinaryJoins A]
variable [CoprodStruct R] [CategoryTheory.HasCoproducts R] [RestrictionCoproducts R]
variable [CoprodStruct A] [CategoryTheory.HasCoproducts A] [RestrictionCoproducts A]
variable [Ranges R] [Ranges A] [Splits A] [JoinInverse A] [LocallyConnected A] [WeakChoice A]

/-- Transport of the actual lifting theorem along equality of the source's
given restriction and its P-category induced restriction. -/
theorem compatible_local_lifting (he : PCategory.inducedRestriction=native)
    (F : RangeFunctor R A) {U : R} (tau : nearProd U U ⟶ U)
    (htau : RecursionCategory.IsTuringMorphism tau) (b : U ≅ coprod U U)
    (hU : F.toFunctor.map (𝟙 U)≠0)
    (lift : ∀ (c c' : Idem U) (hc : Complementary c c'),∃ l : U ⟶ coprod U U,
      F.toFunctor.map l=switchSection (F.mapIdem c) (F.mapIdem c') (F.map_complementary hc) ≫
        (F.comparison U U).hom) :
    Inseparable (Idem.pull (diag U ≫ tau ≫ b.hom) (summand0 U U))
      (Idem.pull (diag U ≫ tau ≫ b.hom) (summand1 U U)) := by
  cases he
  exact local_lifting F tau htau b hU lift

end CategoricalEssentialIncompleteness.LocalConnectedness
