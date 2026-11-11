/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSentenceLiteralChart


/-! # Statement checks in `V46SyntacticSentenceLiteralChartChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.SyntacticSentenceLiteralChart.Checks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

example : CategoryTheory.Iso (C := PredicateCategory T)
    (ConcreteNamedComparison.literalSentenceCarrier T V σ π d)
    (plainCategoricalSyntax T V σ π d).sentenceObject := toSentenceIso T V σ π d

example (word : Obj T M (ConcreteNamedComparison.literalSentenceCarrier T V σ π d)) :
    ((F T M).map (plainCategoricalSyntax T V σ π d).sentenceInclusion
      ((F T M).map (toSentence T V σ π d) word)).val = word.val :=
  toSentence_value T V σ π d M word
end CategoricalEssentialIncompleteness.V46.SyntacticSentenceLiteralChart.Checks
