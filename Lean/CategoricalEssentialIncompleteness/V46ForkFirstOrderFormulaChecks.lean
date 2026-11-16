/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ForkFirstOrderFormula

/-! # Independent checks of fork formula initiality

These checks cover the constructed formula algebra. Parameter stability,
substitution and initial finite derivations remain separate obligations.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46

/-- This includes arbitrary coefficient morphisms; none is assumed monic. -/
example {J : Type u} [Category.{v} J] {I : Type w}
    (c : I → J ⥤ NumericalTuples.Object) (p q : SyntaxPolynomial I) :
    IsInitial (NumericalDiagramSyntax.algebra c p q) := NumericalDiagramSyntax.initial c p q

namespace ForkChecks
open ForkFirstOrderFormula
variable (D : Object)

example (j : WalkingSpan) : (numbers.obj j).support = Set.univ := numbers_full j

example {j k : WalkingSpan} (f : j ⟶ k) : numbers.map f = 𝟙 (numbers.obj j) :=
  numbers_transition f

example (Y : Object) (j : WalkingSpan) :
    ((DiagramInitialAlgebras.diagonal (polynomialDiagram D)).obj Y).obj j =
      (((((numbers.obj j ⨯ numbers.obj j) ⨿ D.obj j) ⨿ Y.obj j) ⨿
        (Y.obj j ⨯ Y.obj j)) ⨿ (numbers.obj j ⨯ Y.obj j)) := polynomial_object D Y j

example (Y : Object) {j k : WalkingSpan} (f : j ⟶ k) :
    ((DiagramInitialAlgebras.diagonal (polynomialDiagram D)).obj Y).map f =
      coprod.map (coprod.map (coprod.map (coprod.map (𝟙 _) (D.map f)) (Y.map f))
        (prod.map (Y.map f) (Y.map f))) (prod.map (𝟙 (numbers.obj j)) (Y.map f)) :=
  polynomial_transition D Y f

example : IsInitial (algebra D) := initial D

example (B : Endofunctor.Algebra (DiagramInitialAlgebras.diagonal (polynomialDiagram D))) :
    (DiagramInitialAlgebras.diagonal (polynomialDiagram D)).map (fold D B).f ≫ B.str =
      (algebra D).str ≫ (fold D B).f := fold_constructor D B

example (B : Endofunctor.Algebra (DiagramInitialAlgebras.diagonal (polynomialDiagram D)))
    {j k : WalkingSpan} (f : j ⟶ k) :
    (algebra D).a.map f ≫ (fold D B).f.app k =
      (fold D B).f.app j ≫ B.a.map f := fold_natural D B f

/-- Every underlying natural morphism satisfying the constructor equation
is the constructed fold. No target evaluator is supplied as an extra hypothesis. -/
example (B : Endofunctor.Algebra (DiagramInitialAlgebras.diagonal (polynomialDiagram D)))
    (m : (algebra D).a ⟶ B.a)
    (hm : (DiagramInitialAlgebras.diagonal (polynomialDiagram D)).map m ≫ B.str =
      (algebra D).str ≫ m) : m = (fold D B).f := fold_underlying_unique D B m hm

end ForkChecks

#print axioms DiagramInitialAlgebras.transition_constructor
#print axioms DiagramInitialAlgebras.transition_unique
#print axioms DiagramInitialAlgebras.transition_id
#print axioms DiagramInitialAlgebras.transition_comp
#print axioms DiagramInitialAlgebras.fold_natural
#print axioms DiagramInitialAlgebras.initial
#print axioms SyntaxCoefficientMorphisms.naturality
#print axioms SyntaxCoefficientMorphisms.component_id
#print axioms SyntaxCoefficientMorphisms.component_comp
#print axioms SyntaxCoefficientMorphisms.jointAction
#print axioms NumericalDiagramSyntax.componentInitial
#print axioms NumericalDiagramSyntax.initial
#print axioms NumericalDiagramSyntax.fold_natural
#print axioms NumericalDiagramSyntax.fold_unique
#print axioms ForkFirstOrderFormula.componentInitial
#print axioms ForkFirstOrderFormula.initial
#print axioms ForkFirstOrderFormula.polynomial_object
#print axioms ForkFirstOrderFormula.polynomial_transition
#print axioms ForkFirstOrderFormula.numbers_full
#print axioms ForkFirstOrderFormula.numbers_transition
#print axioms ForkFirstOrderFormula.fold_constructor
#print axioms ForkFirstOrderFormula.fold_natural
#print axioms ForkFirstOrderFormula.fold_unique
#print axioms ForkFirstOrderFormula.fold_underlying_unique
