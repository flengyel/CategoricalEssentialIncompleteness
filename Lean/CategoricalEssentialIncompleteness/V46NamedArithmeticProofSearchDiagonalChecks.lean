/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticProofSearchDiagonal

/-! # The exact diagonal instance of the actual partial Γ search -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.CoprodStruct
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.NamedArithmeticSignature
open CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch.DiagonalChecks

example (Γ : Carrier) :
    ∃ l : omegaObject 𝗣𝗔 ⟶ coprod (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔),
      ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔],
        (∀ n : M, ¬(
          (SyntacticGeneratedAxioms.theoremCarrier 𝗣𝗔
            variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
              ![NamedArithmeticUnarySubstitution.value ArithmeticDiagonalCodes.alpha.val n] ∧
          (SyntacticGeneratedAxioms.refutationCarrier 𝗣𝗔
            variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
              ![NamedArithmeticUnarySubstitution.value ArithmeticDiagonalCodes.alpha.val n])) →
        Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map l)
          (summand0 (PartialFun.of M) (PartialFun.of M)) =
            setIdem {n : M | (SyntacticGeneratedAxioms.refutationCarrier 𝗣𝗔
              variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
                ![NamedArithmeticUnarySubstitution.value ArithmeticDiagonalCodes.alpha.val n]} ∧
        Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map l)
          (summand1 (PartialFun.of M) (PartialFun.of M)) =
            setIdem {n : M | (SyntacticGeneratedAxioms.theoremCarrier 𝗣𝗔
              variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
                ![NamedArithmeticUnarySubstitution.value ArithmeticDiagonalCodes.alpha.val n]} :=
  diagonal_partial_proof_search Γ

end CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch.DiagonalChecks
