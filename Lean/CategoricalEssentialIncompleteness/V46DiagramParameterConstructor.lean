/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46SliceParameterConstructorComparison

/-! # Parameterizing a constructor commutes with diagram evaluation -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.DiagramParameterConstructor
variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
variable [Regular C] [HasFiniteCoproducts C] [Regular (J ⥤ C)]
local instance (P : C) : Regular (Over P) := RegularSlices.regular P
local instance (P : J ⥤ C) : Regular (Over P) := RegularSlices.regular P
variable {I : Type w} (c : I → J ⥤ C) (P : J ⥤ C) (X : (J ⥤ C) × (J ⥤ C))

/-- A proved ordinary constructor square supplies the full parameter constructor square,
with both recursive sorts and the family maps. -/
theorem square (p : SyntaxPolynomial I) {Y : J ⥤ C}
    (s : (p.mapCoefficients c).eval.obj X ⟶ Y) (j : J)
    (t : (p.mapCoefficients (fun i => (c i).obj j)).eval.obj (X.1.obj j, X.2.obj j) ⟶ Y.obj j)
    (hs : s.app j = DiagramPolynomialComparison.component c X p j ≫ t) :
    (SliceEvaluation.componentFunctor P j).map
        (PolynomialParameterValues.comparison P c X p ≫ (constantFamilyFunctor P).map s) ≫
        (SliceEvaluation.coefficientIso P Y j).hom =
      SliceParameterConstructorComparison.relativeInput c P X p j ≫
        PolynomialParameterValues.comparison (P.obj j) (fun i => (c i).obj j)
          (X.1.obj j, X.2.obj j) p ≫ (constantFamilyFunctor (P.obj j)).map t := by
  rw [Functor.map_comp, Category.assoc,
    SliceParameterConstructorComparison.coefficient_natural P s j, hs, Functor.map_comp]
  simpa only [Category.assoc] using congrArg
    (fun m => m ≫ (constantFamilyFunctor (P.obj j)).map t)
      (SliceParameterConstructorComparison.comparison_square c P X p j)
end CategoricalEssentialIncompleteness.V46.DiagramParameterConstructor
