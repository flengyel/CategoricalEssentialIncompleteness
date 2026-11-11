/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticUnarySubstitution


/-! # Statement checks in `V46NamedArithmeticUnarySubstitutionChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.NamedArithmeticUnarySubstitution
example (α : ArithmeticSemisentence 1) : Primrec (value α : ℕ → ℕ) := value_primrec α
example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (α : ArithmeticSemisentence 1) (n : M) :
    (ConcreteNamedComparison.literalSentenceCarrier 𝗣𝗔 NamedArithmeticSignature.variableSymbols
      NamedArithmeticSignature.functionSymbols NamedArithmeticSignature.relationSymbols NamedArithmeticSignature.bound).val.Evalb
        ![value α n] := value_sentence α n
example (α : ArithmeticSemisentence 1) : SyntacticPredicates.GraphMorphism 𝗣𝗔
    NamedArithmeticSignature.variableSymbols
    (ConcreteNamedComparison.literalSentenceCarrier 𝗣𝗔 NamedArithmeticSignature.variableSymbols
      NamedArithmeticSignature.functionSymbols NamedArithmeticSignature.relationSymbols NamedArithmeticSignature.bound) := morphism α
