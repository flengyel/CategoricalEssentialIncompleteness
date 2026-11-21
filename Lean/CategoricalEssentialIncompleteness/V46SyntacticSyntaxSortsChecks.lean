/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxSorts


/-! # Decidable sort skeletons for parser and value stacks -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SortsChecks
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
example (stack : M) : len (sorts stack) = len stack := len_sorts stack
example (stack : M) : sorts stack = 0 ↔ stack = 0 := sorts_eq_zero stack
example (q : RawPolynomial) (shape left right : M) (h : sorts left = sorts right) :
    remainderKey (refill q shape left) = remainderKey (refill q shape right) :=
  refill_sorts q shape left right h
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SortsChecks
