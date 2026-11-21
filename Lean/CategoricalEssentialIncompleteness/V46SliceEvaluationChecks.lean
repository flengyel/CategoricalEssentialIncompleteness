/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ForkCanonicalParameterTargets

/-! # Evaluation in slices and folds into the canonical target -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
namespace CategoricalEssentialIncompleteness.V46.SliceEvaluationStatementChecks
section General
variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
variable [HasFiniteLimits C] [HasFiniteCoproducts C] {I : Type w}
variable (c : I → J ⥤ C) (P : J ⥤ C)

/-- The required preservation conclusions for evaluation are constructed. -/
example (j : J) : PreservesFiniteLimits (SliceEvaluation.componentFunctor P j) ∧
    PreservesFiniteCoproducts (SliceEvaluation.componentFunctor P j) :=
  ⟨inferInstance, inferInstance⟩

example (X : J ⥤ C) (j : J) :
    (SliceEvaluation.componentFunctor P j).obj (constantFamily P X) ≅
      constantFamily (P.obj j) (X.obj j) := SliceEvaluation.coefficientIso P X j

example (p : SyntaxPolynomial I) : (p.mapCoefficients c).withParameters P =
    p.mapCoefficients (fun i => constantFamily P (c i)) :=
  SlicePolynomialComparison.withParameters_eq c P p

/-- Both recursive carrier families and all labelled coefficients are
arbitrary, including nonconstant and empty families. -/
example (p : SyntaxPolynomial I) (X : Over P × Over P) (j : J) :
    (SliceEvaluation.componentFunctor P j).obj
        ((p.mapCoefficients (fun i => constantFamily P (c i))).eval.obj X) ≅
      (p.mapCoefficients (fun i => constantFamily (P.obj j) ((c i).obj j))).eval.obj
        ((SliceEvaluation.componentFunctor P j).obj X.1,
          (SliceEvaluation.componentFunctor P j).obj X.2) :=
  asIso (SlicePolynomialComparison.component c P p X j)

/-- Compatibility is proved for every parameter transition. It is not an
input to this statement; no monicity or product preservation is imposed. -/
example (p : SyntaxPolynomial I) (X : Over P × Over P) {j k : J} (f : j ⟶ k) :
    SliceEvaluation.transition P
        ((p.mapCoefficients (fun i => constantFamily P (c i))).eval.obj X) f ≫
      SlicePolynomialComparison.component c P p X k =
    (Over.map (P.map f)).map (SlicePolynomialComparison.component c P p X j) ≫
      SlicePolynomialComparison.input c P p X f :=
  SlicePolynomialComparison.transition_square c P p X f

/-- Every global operation has the component constructor square; there is no supplied
component evaluator or naturality premise. -/
example (p : SyntaxPolynomial I) (X : Over P × Over P) (Y : Over P)
    (r : (p.mapCoefficients (fun i => constantFamily P (c i))).eval.obj X ⟶ Y)
    {j k : J} (f : j ⟶ k) :
    SlicePolynomialComparison.input c P p X f ≫
        SlicePolynomialComparison.operation c P p X Y r k =
      (Over.map (P.map f)).map (SlicePolynomialComparison.operation c P p X Y r j) ≫
        SliceEvaluation.transition P Y f :=
  SlicePolynomialComparison.operation_square c P p X Y r f
end General

section Fork
open ForkCanonicalParameterTargets
variable (D P : ForkFirstOrderFormula.Object)

example : polynomial D P = insert P ⋙
    ((ForkFormulaParameterChange.template.mapCoefficients (coefficients D)).withParameters P).eval :=
  polynomial_eq D P

/-- Every target algebra for the chosen global slice polynomial is included. -/
example (B : Endofunctor.Algebra (polynomial D P)) :
    ForkParameterizedFormulaFolds.Algebra D P := target D P B

example (B : Endofunctor.Algebra (polynomial D P)) :
    (fold D P B).left ≫ B.a.hom =
      (ForkParameterizedFormulaFolds.parameterCarrier D P).hom := fold_over D P B

example (B : Endofunctor.Algebra (polynomial D P)) (j : WalkingSpan) :
    (ForkParameterizedFormulaFolds.polynomial D P j).map
        (ForkParameterizedFormulaFolds.componentHom P (fold D P B) j) ≫
      (target D P B).str j =
    (ForkParameterizedFormulaFolds.algebra D P).str j ≫
      ForkParameterizedFormulaFolds.componentHom P (fold D P B) j := fold_constructor D P B j

/-- Uniqueness covers all underlying natural morphisms over P with the
component constructor equations. -/
example (B : Endofunctor.Algebra (polynomial D P))
    (m : ForkParameterizedFormulaFolds.parameterCarrier D P ⟶ B.a)
    (hm : ∀ j, (ForkParameterizedFormulaFolds.polynomial D P j).map
        (ForkParameterizedFormulaFolds.componentHom P m j) ≫ (target D P B).str j =
      (ForkParameterizedFormulaFolds.algebra D P).str j ≫
        ForkParameterizedFormulaFolds.componentHom P m j) : m = fold D P B :=
  fold_underlying_unique D P B m hm

example (B : Endofunctor.Algebra (polynomial D P)) :
    (constantFold D P B).left ≫ B.a.hom =
      (constantFamily P (ForkFirstOrderFormula.algebra D).a).hom := constantFold_over D P B

example (B : Endofunctor.Algebra (polynomial D P)) {j k : WalkingSpan} (f : j ⟶ k) :
    (constantFamily P (ForkFirstOrderFormula.algebra D).a).left.map f ≫
        (constantFold D P B).left.app k =
      (constantFold D P B).left.app j ≫ B.a.left.map f :=
  (constantFold D P B).left.naturality f
end Fork

#print axioms LaxPolynomialComparison.component_product_fst
#print axioms LaxPolynomialComparison.component_product_snd
#print axioms LaxPolynomialComparison.component_sum_inl
#print axioms LaxPolynomialComparison.component_sum_inr
#print axioms LaxPolynomialComparison.component_isIso
#print axioms LaxPolynomialComparison.natural_square
#print axioms SliceEvaluation.post_preservesFiniteCoproducts
#print axioms SliceEvaluation.component_preservesFiniteLimits
#print axioms SliceEvaluation.component_preservesFiniteCoproducts
#print axioms SliceEvaluation.coefficientIso
#print axioms SliceEvaluation.transition
#print axioms SliceEvaluation.transition_left
#print axioms SliceEvaluation.coefficientTransition
#print axioms SliceEvaluation.coefficient_square
#print axioms SlicePolynomialComparison.component
#print axioms SlicePolynomialComparison.component_isIso
#print axioms SlicePolynomialComparison.jointIso
#print axioms SlicePolynomialComparison.withParameters_eq
#print axioms SlicePolynomialComparison.input
#print axioms SlicePolynomialComparison.transition_square
#print axioms SlicePolynomialComparison.operation
#print axioms SlicePolynomialComparison.operation_square
#print axioms ForkCanonicalParameterTargets.polynomial
#print axioms ForkCanonicalParameterTargets.polynomial_eq
#print axioms ForkCanonicalParameterTargets.target
#print axioms ForkCanonicalParameterTargets.fold
#print axioms ForkCanonicalParameterTargets.fold_over
#print axioms ForkCanonicalParameterTargets.fold_constructor
#print axioms ForkCanonicalParameterTargets.fold_underlying_unique
#print axioms ForkCanonicalParameterTargets.constantFold
#print axioms ForkCanonicalParameterTargets.constantFold_over
end CategoricalEssentialIncompleteness.V46.SliceEvaluationStatementChecks
