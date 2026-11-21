/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticFixedSentenceMorphism


/-! # The sentence morphism for a formula with bounded free names -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates SyntacticSyntax NamedArithmeticSignature NamedArithmeticFixedSentenceMorphism
example (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance variableSymbols
      (plainCategoricalSyntax 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound).sentenceObject := theta φ hφ
example (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (n : PredicateInterpretation.Obj M variableSymbols) :
    ((PredicateInterpretation.functor 𝗣𝗔 M).map
      (plainCategoricalSyntax 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound).sentenceInclusion
      ((PredicateInterpretation.functor 𝗣𝗔 M).map (theta φ hφ) n)).val = NamedArithmeticFixedSubstitution.value φ n.val :=
  theta_word_value φ hφ M n
