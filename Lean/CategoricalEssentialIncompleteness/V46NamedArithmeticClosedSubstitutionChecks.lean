/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticClosedSubstitution


/-! # Statement checks in `V46NamedArithmeticClosedSubstitutionChecks` -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates SyntacticSyntax ConcreteNamedSubstitution NamedArithmeticClosedSubstitution
example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) (x replacement word : M)
    (hrep : (Postfix.carrier false (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![replacement])
    (hclosed : freeVariables V σ π d replacement = 0)
    (hw : (Postfix.carrier true (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![word]) :
    substitutionFreeFor V σ π d x replacement word = 1 := substitutionFreeFor_closed V σ π d x replacement word hrep hclosed hw
