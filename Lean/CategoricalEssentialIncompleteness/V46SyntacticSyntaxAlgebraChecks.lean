/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxAlgebra

/-! # The literal postfix algebra has the exact arbitrary-coefficient K type -/

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ) :
    Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)) :=
  postfixAlgebra T (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d)

example (a b : SyntaxPolynomial (PredicateCategory T)) :
    GraphMorphism T (rawCarrier (termCarrier a b) (formulaCarrier a b) a)
      (termCarrier a b) := termConstructorMorphism T a b

example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (a b : SyntaxPolynomial (PredicateCategory T)) (u : M)
    (z : Obj T M (a.eval.obj ((postfixAlgebra T a b).a)))
    (h : (baseRepresentation T (termCarrier a b) (formulaCarrier a b) a).val.Evalb
      ![u, z.val]) :
    ((F T M).map (postfixAlgebra T a b).str.1 z).val = Coding.constructor false a u :=
  postfixTerm_value T M a b u z h
