/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPostfixSemantics


/-! # Statement checks in `V46NamedPostfixSemanticsChecks` -/

@[expose] public section
noncomputable section
universe u
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NamedPostfixSemanticsChecks
open NamedPostfixEncoding NamedPostfixSemantics
variable (σ π : ℕ → Carrier) (d : ℕ) {K : Type u}
variable (functions : ∀ n : Fin (d + 1), Symbols σ n.val → (Fin n.val → K) → K)
  (relations : ∀ n : Fin (d + 1), Symbols π n.val → (Fin n.val → K) → Prop)
example : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d ≃
    (PredicateInterpretation.functor 𝗣𝗔 ℕ).obj
      (SyntacticSyntax.formulaCarrier (termPolynomial σ d) (formulaPolynomial π d)) :=
  formulaModelEquiv σ π d
example (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) (assignment : ℕ → K) :
    Holds functions relations (formulaEquiv σ π d φ) assignment ↔
      φ.Holds functions relations assignment := holds_encoded functions relations φ assignment
example [Nonempty K] (φ : formulaWords σ π d)
    (hφ : Valid functions relations φ) (hn : Valid functions relations (negWord φ)) : False :=
  valid_negation_disjoint functions relations φ hφ hn
end CategoricalEssentialIncompleteness.V46.NamedPostfixSemanticsChecks
