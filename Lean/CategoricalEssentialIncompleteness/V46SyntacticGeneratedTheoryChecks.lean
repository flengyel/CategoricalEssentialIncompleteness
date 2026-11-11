/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticGeneratedTheory

/-! # Actual generated sentence theories with no assumed derivation initiality -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticGeneratedTheory
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
local notation "S" => SyntacticSyntax.plainCategoricalSyntax T V σ π d

example {A : PredicateCategory T} (axioms : A ⟶ (S).sentenceObject) :
    IsInitial (proofAlgebra T V σ π d axioms) := proofInitial T V σ π d axioms

example {A : PredicateCategory T} (axioms : A ⟶ (S).sentenceObject) :
    IsSentenceTheory T V σ π d (image.ι (sentenceConclusion T V σ π d axioms)) :=
  sentence_theory_closed T V σ π d axioms

example {A U : PredicateCategory T} (axioms : A ⟶ (S).sentenceObject)
    (m : U ⟶ (S).sentenceObject) [Mono m] (hm : IsSentenceTheory T V σ π d m)
    (k : A ⟶ U) (hk : k ≫ m = axioms) :
    sentenceTheory T V σ π d axioms ≤ Subobject.mk m :=
  sentence_theory_least T V σ π d axioms m hm k hk

example {A : PredicateCategory T} (axioms : A ⟶ (S).sentenceObject) :
    interpretedObject T (literalSentencePredicate T V σ π d axioms) ≅
      (realization T).obj (image (sentenceConclusion T V σ π d axioms)) :=
  literalSentenceRestrictionSplitting T V σ π d axioms
