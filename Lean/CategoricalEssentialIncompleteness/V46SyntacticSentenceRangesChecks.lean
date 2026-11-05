/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSentenceRanges

/-! # PA-functional sentence programs and their exact source ranges -/

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open FailureOfComposition.TypedRanges FailureOfComposition.UniformIndexQuotient
open FailureOfComposition.ProofSearch FailureOfComposition.ConcreteEvaluator
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSentenceImages
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example {P Fm S : PredicateCategory T} (c : P ⟶ Fm) (j : S ⟶ Fm) :
    𝗣𝗔 ⊢ functionalSentence (sentenceGraph T c j) := sentenceGraph_functional_pa T c j

example {P Fm S : PredicateCategory T} (c : P ⟶ Fm) (j : S ⟶ Fm) :
    Uniform 𝗣𝗔 (eventualGraph (sentenceIndex T c j)) (sentenceGraph T c j) :=
  sentenceIndex_uniform_pa T c j

example {P Fm S : PredicateCategory T} (c : P ⟶ Fm) (j : S ⟶ Fm) :
    rangeArrow T (sentenceProgram T c j) = (theoryIdem T c j).hom :=
  sentenceProgram_range T c j

example {P Fm S : PredicateCategory T} (c : P ⟶ Fm) (j : S ⟶ Fm) :
    rangeArrow T (sentenceProgram T c j) =
      (predicateIdem T (programTheoryCarrier T c j)).hom := sentenceProgram_range_literal T c j

example {P Fm S : PredicateCategory T} (c : P ⟶ Fm) (j : S ⟶ Fm) [Mono j] :
    interpretedObject T (programTheoryCarrier T c j) ≅
      (realization T).obj (image (pullback.snd c j)) := programTheorySplittingIso T c j
