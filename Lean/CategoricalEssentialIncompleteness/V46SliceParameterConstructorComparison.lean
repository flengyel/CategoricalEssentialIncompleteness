/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46PolynomialInputComposition
public import CategoricalEssentialIncompleteness.V46SlicePolynomialComparison
public import CategoricalEssentialIncompleteness.V46NumericalForkPartialMaps

/-! # Evaluation commutes with the actual parameter constructor comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SliceParameterConstructorComparison
variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
variable [Regular C] [HasFiniteCoproducts C] [Regular (J ⥤ C)]
local instance (P : C) : Regular (Over P) := RegularSlices.regular P
local instance (P : J ⥤ C) : Regular (Over P) := RegularSlices.regular P
variable {I : Type w} (c : I → J ⥤ C) (P : J ⥤ C) (X : (J ⥤ C) × (J ⥤ C))

abbrev families : Over P × Over P := (constantFamily P X.1, constantFamily P X.2)
abbrev localFamilies (j : J) : Over (P.obj j) × Over (P.obj j) :=
  (constantFamily (P.obj j) (X.1.obj j), constantFamily (P.obj j) (X.2.obj j))

omit [HasFiniteCoproducts C] [Regular (J ⥤ C)] in
@[reassoc] theorem coefficient_value (Y : J ⥤ C) (j : J) :
    (SliceEvaluation.coefficientIso P Y j).hom.left ≫ prod.snd =
      (prod.snd : P ⨯ Y ⟶ Y).app j :=
  prodComparison_snd ((evaluation J C).obj j) P Y

omit [HasFiniteCoproducts C] [Regular (J ⥤ C)] in
@[reassoc] theorem coefficient_natural {Y Z : J ⥤ C} (r : Y ⟶ Z) (j : J) :
    (SliceEvaluation.componentFunctor P j).map ((constantFamilyFunctor P).map r) ≫
        (SliceEvaluation.coefficientIso P Z j).hom =
      (SliceEvaluation.coefficientIso P Y j).hom ≫
        (constantFamilyFunctor (P.obj j)).map (r.app j) := by
  apply Over.OverMorphism.ext
  change ((evaluation J C).obj j).map (prod.map (𝟙 P) r) ≫
    prodComparison ((evaluation J C).obj j) P Z =
      prodComparison ((evaluation J C).obj j) P Y ≫ prod.map (𝟙 _) (r.app j)
  have h := prodComparison_natural ((evaluation J C).obj j) (𝟙 P) r
  erw [((evaluation J C).obj j).map_id P] at h
  exact h

def relativeInput (p : SyntaxPolynomial I) (j : J) :
    (SliceEvaluation.componentFunctor P j).obj (PolynomialParameterValues.object P c X p) ⟶
      PolynomialParameterValues.object (P.obj j) (fun i => (c i).obj j)
        (X.1.obj j, X.2.obj j) p :=
  LaxPolynomialComparison.input (SliceEvaluation.componentFunctor P j)
    (fun i => (SliceEvaluation.coefficientIso P (c i) j).hom) p (families P X)
    (localFamilies P X j)
    ((SliceEvaluation.coefficientIso P X.1 j).hom, (SliceEvaluation.coefficientIso P X.2 j).hom)

/-- This square compares values of the actual canonical parameter maps. -/
theorem value_square (p : SyntaxPolynomial I) (j : J) :
    ((evaluation J C).obj j).map (PolynomialParameterValues.value P c X p) ≫
        DiagramPolynomialComparison.component c X p j =
      (relativeInput c P X p j).left ≫
        PolynomialParameterValues.value (P.obj j) (fun i => (c i).obj j)
          (X.1.obj j, X.2.obj j) p := by
  let E := (evaluation J C).obj j
  let R := SliceEvaluation.componentFunctor P j
  let χ := fun i => (prod.snd : P ⨯ c i ⟶ c i)
  let γ := fun i => (SliceEvaluation.coefficientIso P (c i) j).hom
  let δ := fun i => (prod.snd : P.obj j ⨯ (c i).obj j ⟶ (c i).obj j)
  have h₁ := PolynomialInputComposition.input_comp (Over.forget P) E
    (c := fun i => constantFamily P (c i)) (d := c) (e := fun i => (c i).obj j)
    χ (fun _ => 𝟙 _)
    p (families P X) X (X.1.obj j, X.2.obj j) (prod.snd, prod.snd) (𝟙 _)
  erw [PolynomialInputComposition.input_id E (c := c)
    (d := fun i => (c i).obj j) (fun _ => 𝟙 _) p X] at h₁
  simp only [Category.comp_id] at h₁
  have h₂ := PolynomialInputComposition.input_comp R (Over.forget (P.obj j))
    (c := fun i => constantFamily P (c i))
    (d := fun i => constantFamily (P.obj j) ((c i).obj j)) (e := fun i => (c i).obj j) γ δ
    p (families P X) (localFamilies P X j) (X.1.obj j, X.2.obj j)
    ((SliceEvaluation.coefficientIso P X.1 j).hom, (SliceEvaluation.coefficientIso P X.2 j).hom)
    (prod.snd, prod.snd)
  have hc : (fun i => (Over.forget (P.obj j)).map (γ i) ≫ δ i) =
      (fun i => E.map (χ i)) := funext (fun i => coefficient_value P (c i) j)
  have hk : ((Over.forget (P.obj j)).prod (Over.forget (P.obj j))).map
      (((SliceEvaluation.coefficientIso P X.1 j).hom,
        (SliceEvaluation.coefficientIso P X.2 j).hom) :
          (R.prod R).obj (families P X) ⟶ localFamilies P X j) ≫
      ((prod.snd, prod.snd) :
        ((Over.forget (P.obj j)).prod (Over.forget (P.obj j))).obj (localFamilies P X j) ⟶
          (X.1.obj j, X.2.obj j)) =
      ((E.map (prod.snd : P ⨯ X.1 ⟶ X.1), E.map (prod.snd : P ⨯ X.2 ⟶ X.2)) :
        ((Over.forget (P.obj j)).prod (Over.forget (P.obj j))).obj
          ((R.prod R).obj (families P X)) ⟶ (X.1.obj j, X.2.obj j)) := by
    apply Prod.ext
    · exact coefficient_value P X.1 j
    · exact coefficient_value P X.2 j
  rw [hc, hk] at h₂
  erw [← PolynomialParameterValues.value_as_input P c X p] at h₁
  erw [← PolynomialParameterValues.value_as_input (P.obj j) (fun i => (c i).obj j)
    (X.1.obj j, X.2.obj j) p] at h₂
  exact h₁.trans h₂.symm

/-- Evaluation preserves the complete constant-family comparison, not
just its carrier or its projection to values. -/
theorem comparison_square (p : SyntaxPolynomial I) (j : J) :
    (SliceEvaluation.componentFunctor P j).map (PolynomialParameterValues.comparison P c X p) ≫
        (SliceEvaluation.coefficientIso P ((p.mapCoefficients c).eval.obj X) j).hom ≫
        (constantFamilyFunctor (P.obj j)).map (DiagramPolynomialComparison.component c X p j) =
      relativeInput c P X p j ≫
        PolynomialParameterValues.comparison (P.obj j) (fun i => (c i).obj j)
          (X.1.obj j, X.2.obj j) p := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w _).trans (Over.w _).symm
  · change (((evaluation J C).obj j).map (PolynomialParameterValues.comparison P c X p).left ≫
      (SliceEvaluation.coefficientIso P ((p.mapCoefficients c).eval.obj X) j).hom.left ≫
      prod.map (𝟙 _) (DiagramPolynomialComparison.component c X p j)) ≫ prod.snd = _
    simp only [Category.assoc, prod.map_snd]
    erw [coefficient_value_assoc P ((p.mapCoefficients c).eval.obj X) j
      (DiagramPolynomialComparison.component c X p j), ← Functor.map_comp_assoc]
    simpa only [PolynomialParameterValues.value, Over.comp_left, Category.assoc] using
      value_square c P X p j

end CategoricalEssentialIncompleteness.V46.SliceParameterConstructorComparison
