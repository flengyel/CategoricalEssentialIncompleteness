/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticModelOccurrences


/-! # Statement checks in `V46NamedArithmeticModelOccurrencesChecks` -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates SyntacticSyntax SyntacticSyntax.Coding
open NamedPostfixEncoding NamedArithmeticModelCoding NamedArithmeticModelOccurrences
example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (σ π : ℕ → Carrier) (d : ℕ) (k : Fin (d+1)) (s : Symbols σ k.val) (c : Fin k.val → M)
    (hc : ∀ i,(Postfix.carrier false (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![c i]) :
    ConcreteNamedSubstitution.freeVariables variableCarrier σ π d
      (constructor false (termPolynomial σ d)
        ⟪NamedArithmeticModelCoding.arityInput d k ⟪(s.val : M),NamedArithmeticModelCoding.childTuple k.val c⟫,1⟫) =
      gatherTuple k.val (fun i => ConcreteNamedSubstitution.freeVariables variableCarrier σ π d (c i)) :=
  function_occurrences σ π d k s c hc
