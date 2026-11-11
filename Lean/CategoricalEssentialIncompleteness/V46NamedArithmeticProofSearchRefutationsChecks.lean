/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticProofSearchRefutations

/-! # Actual Γ image predicates, with no assumed comparison -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.NamedArithmeticSignature
open CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch.RefutationChecks

example (Γ : Carrier) (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (n : M) :
    (negative Γ φ).val.Evalb ![n] ↔
      (SyntacticGeneratedAxioms.refutationCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
          ![NamedArithmeticFixedSubstitution.value φ n] :=
  negative_refutation_image M Γ φ hφ n

#check @actual_partial_proof_search

end CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch.RefutationChecks
