/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticSubstitutionOccurrences


/-! # Free variables after substitution of a closed term -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates NamedPostfixEncoding NamedArithmeticModelCoding NamedArithmeticModelSubstitution
open NamedArithmeticSubstitutionOccurrences
example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (σ π : ℕ → Carrier) (d : ℕ) (x replacement name : M)
    (hrep : (SyntacticSyntax.Postfix.carrier false (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![replacement])
    (hclosed : ConcreteNamedSubstitution.freeVariables variableCarrier σ π d replacement = 0)
    (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    ConcreteNamedSubstitution.member name
        (ConcreteNamedSubstitution.freeVariables variableCarrier σ π d (formulaOutput x replacement φ)) = 1 ↔
      name ≠ x ∧ ConcreteNamedSubstitution.member name
        (ConcreteNamedSubstitution.freeVariables variableCarrier σ π d (formulaWord φ)) = 1 :=
  formulaOutput_member_iff σ π d x replacement hrep hclosed φ name
