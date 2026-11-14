/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalLists
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Finite geometry of constant families and evaluation in ordinary slices -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SliceBaseChangeGeometry

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C] [HasFiniteCoproducts C]

def constantHomEquiv (U : C) (X : Over U) (Y : C) :
    (X.left ⟶ Y) ≃ (X ⟶ constantFamily U Y) where
  toFun f := Over.homMk (prod.lift X.hom f) (prod.lift_fst _ _)
  invFun g := g.left ≫ prod.snd
  left_inv f := prod.lift_snd _ _
  right_inv g := by
    apply Over.OverMorphism.ext
    apply prod.hom_ext
    · exact (prod.lift_fst _ _).trans (Over.w g).symm
    · exact prod.lift_snd _ _

/-- The constant-family functor is the ordinary right adjoint to forgetting
an object's total projection to the parameter. -/
def forgetAdjunction (U : C) : Over.forget U ⊣ constantFamilyFunctor U :=
  Adjunction.mkOfHomEquiv {
    homEquiv := constantHomEquiv U
    homEquiv_naturality_left_symm := by
      intro X X' Y f g
      exact Category.assoc f.left g.left prod.snd
    homEquiv_naturality_right := by
      intro X Y Y' f g
      apply Over.OverMorphism.ext
      apply prod.hom_ext
      · exact (Over.w _).trans (Over.w _).symm
      · simp [constantHomEquiv, constantFamilyFunctor, constantFamily]
  }

omit [HasFiniteCoproducts C] in
theorem constant_preservesFiniteLimits (U : C) :
    PreservesFiniteLimits (constantFamilyFunctor U) := by
  let : (constantFamilyFunctor U).IsRightAdjoint := ⟨Over.forget U, ⟨forgetAdjunction U⟩⟩
  infer_instance

variable {Z U : C} (point : Z ⟶ U)

def evaluation (_hZ : IsTerminal Z) : Over U ⥤ C := Over.pullback point ⋙ Over.forget Z

omit [HasFiniteCoproducts C] in
theorem evaluation_preservesFiniteLimits (hZ : IsTerminal Z) :
    PreservesFiniteLimits (evaluation point hZ) := by
  let : (Over.forget Z).IsEquivalence := (Over.equivalenceOfIsTerminal hZ).isEquivalence_functor
  let : PreservesFiniteLimits (Over.forget Z) := inferInstance
  dsimp only [evaluation]
  infer_instance

end CategoricalEssentialIncompleteness.V46.SliceBaseChangeGeometry
