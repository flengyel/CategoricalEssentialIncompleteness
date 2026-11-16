/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46DiagramPolynomialComparison
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over

/-! # Evaluation of arbitrary families over a parameter diagram -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u₁ v₁ u₂ v₂ u₃ v₃
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SliceEvaluation
section Post
variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
variable [HasFiniteCoproducts A] [HasFiniteCoproducts B]

/-- Finite coproducts in slices are created by their forgetful functors. -/
instance post_preservesFiniteCoproducts (F : A ⥤ B) [PreservesFiniteCoproducts F] (P : A) :
    PreservesFiniteCoproducts (Over.post (X := P) F) where
  preserves n := by
    have : PreservesColimitsOfShape (Discrete (Fin n))
        (Over.post (X := P) F ⋙ Over.forget (F.obj P)) :=
      show PreservesColimitsOfShape (Discrete (Fin n)) (Over.forget P ⋙ F) from inferInstance
    exact preservesColimitsOfShape_of_reflects_of_preserves
      (Over.post (X := P) F) (Over.forget (F.obj P))
end Post

variable {J : Type u₁} [Category.{v₁} J] {C : Type u₂} [Category.{v₂} C]
variable [HasFiniteLimits C] [HasFiniteCoproducts C] (P : J ⥤ C)

abbrev componentFunctor (j : J) : Over P ⥤ Over (P.obj j) :=
  Over.post ((evaluation J C).obj j)

instance component_preservesFiniteLimits (j : J) :
    PreservesFiniteLimits (componentFunctor P j) := inferInstance

instance component_preservesFiniteCoproducts (j : J) :
    PreservesFiniteCoproducts (componentFunctor P j) := inferInstance

/-- Evaluation of the global chosen constant family is canonically
isomorphic to the chosen constant family at each component. -/
def coefficientIso (X : J ⥤ C) (j : J) :
    (componentFunctor P j).obj (constantFamily P X) ≅
      constantFamily (P.obj j) (X.obj j) :=
  Over.isoMk (asIso (prodComparison ((evaluation J C).obj j) P X))
    (prodComparison_fst ((evaluation J C).obj j) P X)

/-- This is postcomposition of evaluation's actual natural transformation. -/
def transition (X : Over P) {j k : J} (f : j ⟶ k) :
    (Over.map (P.map f)).obj ((componentFunctor P j).obj X) ⟶
      (componentFunctor P k).obj X :=
  (Over.postMap (X := P) ((evaluation J C).map f)).app X

omit [HasFiniteLimits C] [HasFiniteCoproducts C] in
@[simp] theorem transition_left (X : Over P) {j k : J} (f : j ⟶ k) :
    (transition P X f).left = X.left.map f := rfl

/-- The parameter and coefficient transitions may both identify elements. -/
def coefficientTransition (X : J ⥤ C) {j k : J} (f : j ⟶ k) :
    (Over.map (P.map f)).obj (constantFamily (P.obj j) (X.obj j)) ⟶
      constantFamily (P.obj k) (X.obj k) :=
  Over.homMk (prod.map (P.map f) (X.map f)) (by simp [constantFamily])

omit [HasFiniteCoproducts C] in
/-- Compatibility of the actual coefficient isomorphisms with transitions
is proved, rather than supplied as an extra hypothesis. -/
theorem coefficient_square (X : J ⥤ C) {j k : J} (f : j ⟶ k) :
    transition P (constantFamily P X) f ≫ (coefficientIso P X k).hom =
      (Over.map (P.map f)).map (coefficientIso P X j).hom ≫
        coefficientTransition P X f := by
  apply Over.OverMorphism.ext
  change (P ⨯ X).map f ≫ prodComparison ((evaluation J C).obj k) P X =
    prodComparison ((evaluation J C).obj j) P X ≫ prod.map (P.map f) (X.map f)
  apply prod.hom_ext
  · erw [Category.assoc, prodComparison_fst, Category.assoc,
      prod.map_fst, ← Category.assoc, prodComparison_fst]
    exact (prod.fst : P ⨯ X ⟶ P).naturality f
  · erw [Category.assoc, prodComparison_snd, Category.assoc,
      prod.map_snd, ← Category.assoc, prodComparison_snd]
    exact (prod.snd : P ⨯ X ⟶ X).naturality f

end CategoricalEssentialIncompleteness.V46.SliceEvaluation
