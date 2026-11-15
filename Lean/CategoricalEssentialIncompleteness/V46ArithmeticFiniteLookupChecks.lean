/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticFiniteLookup

/-! # Statement checks for internal finite lookup -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace CategoricalEssentialIncompleteness.V46.ArithmeticFiniteLookup.Checks

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example : ∀ x l : M, ∃! y : M, graph.val.Evalb ![y, x, l] := total_model

example (x l : M) : lookup x l = 1 ↔ ∃ i < len l, x = nth l i := lookup_one_iff x l

example (y x l : M) :
    graph.val.Evalb ![y, x, l] ↔ recursiveGraph.val.Evalb ![y, x, l] :=
  graph_iff_recursiveGraph y x l

example (A B : FiniteSigmaOne.Carrier)
    (hab : ∀ x : M, A.val.Evalb ![x] → ¬B.val.Evalb ![x]) :
    ∀ l : M, (FiniteSigmaOne.allEntriesCondition A).Evalb ![l] →
      ∀ x : M, B.val.Evalb ![x] → graph.val.Evalb ![0, x, l] :=
  negative_label_value A B hab

example : 𝗣𝗔 ⊢ totalSentence := total_PA
example : 𝗣𝗔 ⊢ recursiveComparisonSentence := recursive_comparison_PA
example (A B : FiniteSigmaOne.Carrier) : 𝗣𝗔 ⊢ negativeLabelSentence A B := negative_label_PA A B
example : Primrec₂ (lookup : ℕ → ℕ → ℕ) := lookup_primrec

#print axioms total_PA
#print axioms recursive_comparison_PA
#print axioms negative_label_PA
#print axioms lookup_primrec

end CategoricalEssentialIncompleteness.V46.ArithmeticFiniteLookup.Checks
