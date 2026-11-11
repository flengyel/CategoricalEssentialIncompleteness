/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxConservation


/-! # Statement checks in `V46SyntacticSyntaxConservationChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Postfix

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.ConservationChecks
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (a b : RawPolynomial) (word out : M) (h : run a b word 1 = out + 1) :
    stackWord out = word := run_word a b word out h

example (formula : Bool) (a b : RawPolynomial) (word : M) :
    (carrier formula a b).val.Evalb ![word] ↔
      (coefficients a b).val.Evalb ![word] ∧ ∃ stored : M,
        run a b word 1 = adjoin ⟪stored, if formula then 1 else 0⟫ 0 + 1 :=
  carrier_iff_singleton formula a b word
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.ConservationChecks
