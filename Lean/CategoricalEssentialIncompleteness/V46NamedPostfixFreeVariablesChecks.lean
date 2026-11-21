/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPostfixFreeVariables


/-! # The standard occurrence algorithm computes named free variables -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NamedPostfixFreeVariablesChecks
open NamedPostfixEncoding SyntacticSyntax.NatVectors
variable (σ π : ℕ → Carrier) (d : ℕ)
example (r : NamedFiniteSyntax.Term (Symbols σ) d) :
    ConcreteNamedSubstitution.freeVariables variableCarrier σ π d (termCode r) = pack r.freeVariables :=
  freeVariables_termCode π r
example (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    ConcreteNamedSubstitution.freeVariables variableCarrier σ π d (formulaCode φ) = pack φ.freeVariables :=
  freeVariables_formulaCode φ
example (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    ConcreteNamedSubstitution.freeVariables variableCarrier σ π d (formulaCode φ) = 0 ↔
      φ.freeVariables = [] := sentence_formulaCode_iff φ
end CategoricalEssentialIncompleteness.V46.NamedPostfixFreeVariablesChecks
