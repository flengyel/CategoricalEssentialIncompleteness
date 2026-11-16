/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ForkParameterizedFormulaFolds

/-! # Independent checks of natural parameterized formula folds

The comparison with the canonical two-sort syntax interface, stable lists,
substitution and finite derivations remain separate obligations.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46

section Generic
variable {C : Type u} [Category.{v} C] [Regular C] [HasFiniteCoproducts C]
local instance (P : C) : Regular (Over P) := RegularSlices.regular P
variable {I : Type w} {c d : I → C} {P Q : C}

/-- Every labelled polynomial and arbitrary parameter and coefficient
morphisms are included. Neither kind of morphism is assumed monic. -/
example (b : P ⟶ Q) (h : ∀ i, c i ⟶ d i) (X Y : C × C) (k : X ⟶ Y)
    (p : SyntaxPolynomial I) :
    PolynomialParameterSquares.relativeInput b h X Y k p ≫
        PolynomialParameterValues.comparison Q d Y p =
      (Over.map b).map (PolynomialParameterValues.comparison P c X p) ≫
        PolynomialParameterSquares.familyMap b
          (PolynomialParameterSquares.baseInput h X Y k p) :=
  PolynomialParameterSquares.comparison_square b h X Y k p
end Generic

open ForkFirstOrderFormula

/-- The reduction guard retains the exact original numerical algebra. -/
example (N D : C) : pairAlgebra N D = (NumericalSyntax.data .unit (expression N D)).1 :=
  pairAlgebra_def N D

example (N D : C) : IsInitial (pairAlgebra N D) := pairInitial N D

example (N D P : C) : IsInitial (SyntaxPolynomial.algebraWithParameters
    .unit (expression N D) (pairAlgebra N D) P) := pairStable N D P

/-- This source constructor square has no supplied compatibility premise. -/
example (D P : Object) {j l : WalkingSpan} (f : j ⟶ l) :
    (ForkFormulaParameterChange.comparison (numbers.obj j) (P.map f) (D.map f)).app
        (constantFamily (P.obj j) (componentAlgebra (numbers.obj j) (D.obj j)).a) ≫
      (ForkFormulaParameterComponents.polynomial (numbers.obj l) (D.obj l) (P.obj l)).map
        (ForkFormulaTransitionSquares.parameterMap (numbers.obj j) (D.obj j) (D.obj l)
          (P.obj j) (P.obj l) (P.map f) ((ForkFirstOrderFormula.algebra D).a.map f)) ≫
      (ForkFormulaParameterComponents.algebra (numbers.obj l) (D.obj l) (P.obj l)).str =
    (Over.map (P.map f)).map
        (ForkFormulaParameterComponents.algebra (numbers.obj j) (D.obj j) (P.obj j)).str ≫
      ForkFormulaTransitionSquares.parameterMap (numbers.obj j) (D.obj j) (D.obj l)
        (P.obj j) (P.obj l) (P.map f) ((ForkFirstOrderFormula.algebra D).a.map f) :=
  ForkFormulaTransitionSquares.fork_source_square D P f

namespace ParameterizedChecks
open ForkParameterizedFormulaFolds
variable (D P : Object)

/-- Both diagrams are arbitrary, including nonconstant parameter families
and atom-identifying transitions. -/
example : IsInitial (algebra D P) := initial D P

example : parameterCarrier D P ≅ constantFamily P (ForkFirstOrderFormula.algebra D).a :=
  parameterCarrierIso D P

example (B : Algebra D P) {j l : WalkingSpan} (f : j ⟶ l) :
    (parameterCarrierFunctor D P).map f ≫ (componentFold D P B l).f.left =
      (componentFold D P B j).f.left ≫ B.carrier.left.map f := fold_natural D P B f

example (B : Algebra D P) :
    (fold D P B).f.left ≫ B.carrier.hom = (parameterCarrier D P).hom ∧
    ∀ j, (polynomial D P j).map (componentHom P (fold D P B).f j) ≫ B.str j =
      (algebra D P).str j ≫ componentHom P (fold D P B).f j :=
  ⟨fold_over D P B, fold_constructor D P B⟩

/-- Every underlying natural morphism over P with the constructor laws is
included in the uniqueness quantifier. -/
example (B : Algebra D P) (m : (algebra D P).carrier ⟶ B.carrier)
    (hm : ∀ j, (polynomial D P j).map (componentHom P m j) ≫ B.str j =
      (algebra D P).str j ≫ componentHom P m j) : m = (fold D P B).f :=
  fold_underlying_unique D P B m hm
end ParameterizedChecks

#print axioms ForkFirstOrderFormula.pairAlgebra_def
#print axioms ForkFirstOrderFormula.pairInitial
#print axioms ForkFirstOrderFormula.pairStable
#print axioms LaxPolynomialComparison.input_product_fst
#print axioms LaxPolynomialComparison.input_product_snd
#print axioms LaxPolynomialComparison.input_sum_inl
#print axioms LaxPolynomialComparison.input_sum_inr
#print axioms PolynomialParameterValues.comparison
#print axioms PolynomialParameterValues.value_product_fst
#print axioms PolynomialParameterValues.value_product_snd
#print axioms PolynomialParameterValues.value_sum_inl
#print axioms PolynomialParameterValues.value_sum_inr
#print axioms PolynomialParameterSquares.value_square
#print axioms PolynomialParameterSquares.comparison_square
#print axioms ForkFormulaSquareTransport.parameter_structure
#print axioms ForkFormulaSquareTransport.relative_input
#print axioms ForkFormulaSquareTransport.constructor_square
#print axioms ForkFormulaTransitionSquares.source_square
#print axioms ForkFormulaTransitionSquares.base_input
#print axioms ForkFormulaTransitionSquares.fork_source_square
#print axioms ForkParameterizedFormulaFolds.algebra
#print axioms ForkParameterizedFormulaFolds.fold
#print axioms ForkParameterizedFormulaFolds.fold_natural
#print axioms ForkParameterizedFormulaFolds.initial
#print axioms ForkParameterizedFormulaFolds.parameterCarrierIso
#print axioms ForkParameterizedFormulaFolds.fold_over
#print axioms ForkParameterizedFormulaFolds.fold_constructor
#print axioms ForkParameterizedFormulaFolds.fold_underlying_unique
