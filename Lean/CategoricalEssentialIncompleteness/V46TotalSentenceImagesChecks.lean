/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46TotalSentenceImages

/-! # Literal source sentence idempotents for arbitrary total-split arrows -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.TotalSentenceImages
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example {P Fm S : TotalSplit T} (c : P ⟶ Fm) (j : S ⟶ Fm) [Mono j] :
    interpretedObject T (sentencePredicate T c j) ≅ image (pullback.snd c j) :=
  sentenceSplittingIso T c j

example {P Fm S : TotalSplit T} (c : P ⟶ Fm) (j : S ⟶ Fm) :
    (sentencePullbackIso T c j).hom ≫
      (predicateEquivalence T).functor.map
        (pullback.snd (sourceConclusion T c) (sourceSentence T j)) ≫
      ((predicateEquivalence T).counitIso.app S).hom = pullback.snd c j :=
  sentencePullbackIso_snd T c j

example {P Fm S : TotalSplit T} (c : P ⟶ Fm) (j : S ⟶ Fm) :
    (sourceSentenceImageIso T c j).hom ≫ image.ι (pullback.snd c j) =
      (predicateEquivalence T).functor.map (image.ι
        (pullback.snd (sourceConclusion T c) (sourceSentence T j))) ≫
      ((predicateEquivalence T).counitIso.app S).hom := sourceSentenceImageIso_over T c j
