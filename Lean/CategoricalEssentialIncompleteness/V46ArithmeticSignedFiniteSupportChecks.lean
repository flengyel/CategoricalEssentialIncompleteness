/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticSignedFiniteSupport

/-! # Statement checks at arbitrary internal support lengths -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace CategoricalEssentialIncompleteness.V46.ArithmeticSignedFiniteSupport.Checks

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (a b : M)
    (ha : (FiniteSigmaOne.allEntriesCondition ArithmeticDiagonalCodes.alpha).Evalb ![a])
    (hb : (FiniteSigmaOne.allEntriesCondition ArithmeticDiagonalCodes.alpha).Evalb ![b]) :
    ∀ x : M, ArithmeticDiagonalCodes.beta.val.Evalb ![x] →
      ArithmeticFiniteLookup.graph.val.Evalb ![0, x, SyntacticSyntax.Words.append a b] :=
  negative_on_combined_support a b ha hb

example (a b x : M) :
    (MemVec x a → ArithmeticFiniteLookup.graph.val.Evalb
      ![1, x, SyntacticSyntax.Words.append a b]) ∧
    (MemVec x b → ArithmeticFiniteLookup.graph.val.Evalb
      ![1, x, SyntacticSyntax.Words.append a b]) :=
  ⟨positive_from_left x a b, positive_from_right x a b⟩

example : 𝗣𝗔 ⊢ negativeSentence := negative_PA

#print axioms mem_append
#print axioms all_entries_append
#print axioms negative_on_combined_support
#print axioms negative_PA

end CategoricalEssentialIncompleteness.V46.ArithmeticSignedFiniteSupport.Checks
