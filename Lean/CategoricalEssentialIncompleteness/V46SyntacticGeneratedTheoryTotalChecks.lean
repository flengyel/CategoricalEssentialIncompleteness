/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticGeneratedTheoryTotal

/-! # Total-split sentence theories and their source idempotent -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticGeneratedTheoryTotal
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : TotalSplit T) (σ π : ℕ → TotalSplit T) (d : ℕ)
local notation "S" => SyntacticSyntax.plainTotalCategoricalSyntax T V σ π d

example {A : TotalSplit T} (axioms : A ⟶ (S).sentenceObject) :
    IsInitial (proofAlgebra T V σ π d axioms) := proofInitial T V σ π d axioms

example {A : TotalSplit T} (axioms : A ⟶ (S).sentenceObject) :
    IsSentenceTheory T V σ π d (image.ι (sentenceConclusion T V σ π d axioms)) :=
  sentence_theory_closed T V σ π d axioms

example {A U : TotalSplit T} (axioms : A ⟶ (S).sentenceObject)
    (m : U ⟶ (S).sentenceObject) [Mono m] (hm : IsSentenceTheory T V σ π d m)
    (k : A ⟶ U) (hk : k ≫ m = axioms) :
    sentenceTheory T V σ π d axioms ≤ Subobject.mk m :=
  sentence_theory_least T V σ π d axioms m hm k hk

example {A : TotalSplit T} (axioms : A ⟶ (S).sentenceObject) :
    interpretedObject T (sentenceSourceCarrier T V σ π d axioms) ≅
      image (sentenceConclusion T V σ π d axioms) := sentenceSourceIso T V σ π d axioms
