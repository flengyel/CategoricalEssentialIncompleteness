/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticModelSubstitution


/-! # A fixed finite source formula may receive a nonstandard closed term -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates NamedPostfixEncoding NamedArithmeticModelCoding NamedArithmeticModelSubstitution
example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {σ π : ℕ → Carrier} {d : ℕ} (x replacement : M)
    (hrep : (SyntacticSyntax.Postfix.carrier false (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![replacement])
    (hclosed : ConcreteNamedSubstitution.freeVariables variableCarrier σ π d replacement = 0)
    (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    ConcreteNamedSubstitution.substitutionResult variableCarrier σ π d x replacement (formulaWord φ) =
      ConcreteNamedSubstitution.ok (formulaOutput x replacement φ) := formulaResult_eq x replacement hrep hclosed φ
