/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46NumericalCanonicalDiagramSyntax
public import CategoricalEssentialIncompleteness.V46DiagramDecidableVariables

/-! # Canonical diagram syntax and decidable variable equality -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u₁ v₁ u₂ v₂ w
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
namespace CategoricalEssentialIncompleteness.V46.CanonicalDiagramSyntaxStatementChecks

section Comparison
variable {J : Type u₁} [Category.{v₁} J] {C : Type u₂} [Category.{v₂} C]
variable [HasFiniteProducts C] [HasFiniteCoproducts C] {I : Type w}
variable (c : I → J ⥤ C) (X : (J ⥤ C) × (J ⥤ C)) (p : SyntaxPolynomial I)

example (j : J) : ((p.mapCoefficients c).eval.obj X).obj j ≅
    (p.mapCoefficients (fun i => (c i).obj j)).eval.obj (X.1.obj j, X.2.obj j) :=
  asIso (DiagramPolynomialComparison.component c X p j)

/-- Every coefficient transition and both recursive transitions occur. -/
example {j k : J} (f : j ⟶ k) :
    ((p.mapCoefficients c).eval.obj X).map f ≫
        DiagramPolynomialComparison.component c X p k =
      DiagramPolynomialComparison.component c X p j ≫
        ((p.mapCoefficients (fun i => (c i).obj j)).eval.map (X.1.map f, X.2.map f) ≫
          SyntaxCoefficientMorphisms.component (fun i => (c i).map f) p
            (X.1.obj k, X.2.obj k)) :=
  (DiagramPolynomialComparison.component_transition c X p f).trans
    (congrArg (fun n => DiagramPolynomialComparison.component c X p j ≫ n)
      (DiagramPolynomialComparison.transition_eq c X p f))
end Comparison

section Initiality
open NumericalCanonicalDiagramSyntax
variable {J : Type u₁} [Category.{v₁} J] {I : Type w}
variable (c : I → J ⥤ NumericalTuples.Object) (p q : SyntaxPolynomial I)

/-- Both polynomial templates and every coefficient diagram are arbitrary. -/
example : IsInitial (algebra c p q) := initial c p q

example : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
    (p.mapCoefficients c) (q.mapCoefficients c)) ≌
      Endofunctor.Algebra (DiagramInitialAlgebras.diagonal
        (NumericalDiagramSyntax.polynomials c p q)) := algebraEquivalence c p q

example (B : Endofunctor.Algebra (polynomial c p q)) :
    (polynomial c p q).map (fold c p q B).f ≫ B.str =
      (algebra c p q).str ≫ (fold c p q B).f := fold_constructor c p q B

/-- Every pair of underlying natural carrier morphisms with the constructor
law is covered, without a supplied evaluator or initiality hypothesis. -/
example (B : Endofunctor.Algebra (polynomial c p q))
    (m : (algebra c p q).a ⟶ B.a)
    (hm : (polynomial c p q).map m ≫ B.str = (algebra c p q).str ≫ m) :
    m = (fold c p q B).f := fold_underlying_unique c p q B m hm

example (V : J ⥤ NumericalTuples.Object) (σ π : ℕ → J ⥤ NumericalTuples.Object) (d : ℕ) :
    IsInitial (syntaxData V σ π d).1 := (syntaxData V σ π d).2

/-- The fork signature has no function symbols and arbitrary nullary predicates. The
statement uses the exact canonical expressions. -/
example (D : ForkFirstOrderFormula.Object) :
    Σ A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (SyntaxPolynomial.termExpression ForkFirstOrderFormula.numbers
        (fun _ => ⊥_ ForkFirstOrderFormula.Object) 0)
      (SyntaxPolynomial.formulaExpression ForkFirstOrderFormula.numbers (fun _ => D) 0)),
      IsInitial A :=
  syntaxData ForkFirstOrderFormula.numbers (fun _ => ⊥_ ForkFirstOrderFormula.Object)
    (fun _ => D) 0
end Initiality

section Variables
variable {J : Type u₁} [Category.{v₁} J] {C : Type u₂} [Category.{v₂} C]
variable [HasFiniteLimits C] [HasFiniteCoproducts C]

example {V : C} (S : DecidableVariables V) :
    DecidableVariables ((Functor.const J).obj V) := DiagramDecidableVariables.constant S

/-- The true injection is explicitly the second injection. -/
example : IsPullback
    (prod.lift (𝟙 ForkFirstOrderFormula.numbers) (𝟙 ForkFirstOrderFormula.numbers))
    (terminal.from ForkFirstOrderFormula.numbers) DiagramDecidableVariables.fork.test
    (coprod.inr : ⊤_ ForkFirstOrderFormula.Object ⟶
      (⊤_ ForkFirstOrderFormula.Object) ⨿ (⊤_ ForkFirstOrderFormula.Object)) :=
  DiagramDecidableVariables.fork_diagonal
end Variables

#print axioms DiagramPolynomialComparison.evaluation_preservesFiniteProducts
#print axioms DiagramPolynomialComparison.evaluation_preservesFiniteCoproducts
#print axioms DiagramPolynomialComparison.component
#print axioms DiagramPolynomialComparison.component_isIso
#print axioms DiagramPolynomialComparison.transition
#print axioms DiagramPolynomialComparison.component_product_fst
#print axioms DiagramPolynomialComparison.component_product_snd
#print axioms DiagramPolynomialComparison.component_sum_inl
#print axioms DiagramPolynomialComparison.component_sum_inr
#print axioms DiagramPolynomialComparison.component_transition
#print axioms DiagramPolynomialComparison.transition_eq
#print axioms SyntaxPolynomial.mapCoefficients_id
#print axioms NumericalCanonicalDiagramSyntax.comparisonHom
#print axioms NumericalCanonicalDiagramSyntax.comparisonHom_isIso
#print axioms NumericalCanonicalDiagramSyntax.polynomialIso
#print axioms NumericalCanonicalDiagramSyntax.algebraEquivalence
#print axioms NumericalCanonicalDiagramSyntax.algebra
#print axioms NumericalCanonicalDiagramSyntax.initial
#print axioms NumericalCanonicalDiagramSyntax.constructorIso
#print axioms NumericalCanonicalDiagramSyntax.fold
#print axioms NumericalCanonicalDiagramSyntax.fold_constructor
#print axioms NumericalCanonicalDiagramSyntax.fold_underlying_unique
#print axioms NumericalCanonicalDiagramSyntax.syntaxData
#print axioms DiagramDecidableVariables.terminalIso
#print axioms DiagramDecidableVariables.booleanIso
#print axioms DiagramDecidableVariables.productIso
#print axioms DiagramDecidableVariables.booleanIso_inr
#print axioms DiagramDecidableVariables.mapped
#print axioms DiagramDecidableVariables.constant
#print axioms DiagramDecidableVariables.fork
#print axioms DiagramDecidableVariables.fork_diagonal
end CategoricalEssentialIncompleteness.V46.CanonicalDiagramSyntaxStatementChecks
