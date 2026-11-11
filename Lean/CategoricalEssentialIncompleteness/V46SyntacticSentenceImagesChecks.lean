/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSentenceImages

/-! # Formula-code sentence images and their actual source restriction splitting -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSentenceImages
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example {P Fm S : PredicateCategory T} (c : P ⟶ Fm) (j : S ⟶ Fm) [Mono j] :
    CategoryTheory.Iso (C := PredicateCategory T)
      (image (pullback.snd c j)) (theoryCarrier T c j) := sentenceImageIso T c j

example {P Fm S : PredicateCategory T} (c : P ⟶ Fm) (j : S ⟶ Fm) [Mono j] :
    interpretedObject T (theoryCarrier T c j) ≅
      (realization T).obj (image (pullback.snd c j)) := theorySplittingIso T c j
