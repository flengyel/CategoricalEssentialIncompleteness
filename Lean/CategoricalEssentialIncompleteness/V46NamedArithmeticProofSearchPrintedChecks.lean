/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticProofSearchPrinted

/-! # Full quantifier and ProvΓ(NegΘ) checks for printed Lemma 7.2 -/

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

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch.PrintedChecks

example (Γ : Carrier) (φ : Formula) (M : Type)
    [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] :
    (SyntacticModel.modelFunctor 𝗣𝗔 M).map (ell Γ φ) ≫
      ((SyntacticModel.modelRangeFunctor 𝗣𝗔 M).comparison
        (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)).inv =
      (SyntacticModel.modelFunctor 𝗣𝗔 M).map (ell Γ φ) :=
  ell_comparison_inv Γ φ M

example (Γ : Carrier) (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    ∃ l : omegaObject 𝗣𝗔 ⟶ coprod (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔),
      ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔],
        (∀ n : M, ¬(
          (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
            variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
              ![NamedArithmeticFixedSubstitution.value φ n] ∧
          (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
            variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
              ![negationWord M (NamedArithmeticFixedSubstitution.value φ n)])) →
        Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map l ≫
          ((SyntacticModel.modelRangeFunctor 𝗣𝗔 M).comparison
            (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)).inv)
          (summand0 (PartialFun.of M) (PartialFun.of M)) =
            setIdem {n : M | (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
              variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
                ![negationWord M (NamedArithmeticFixedSubstitution.value φ n)]} ∧
        Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map l ≫
          ((SyntacticModel.modelRangeFunctor 𝗣𝗔 M).comparison
            (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)).inv)
          (summand1 (PartialFun.of M) (PartialFun.of M)) =
            setIdem {n : M | (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
              variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
                ![NamedArithmeticFixedSubstitution.value φ n]} :=
  printed_partial_proof_search Γ φ hφ

example (Γ : Carrier) :
    ∃ l : omegaObject 𝗣𝗔 ⟶ coprod (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔),
      ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔],
        (∀ n : M, ¬(
          (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
            variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
              ![NamedArithmeticUnarySubstitution.value ArithmeticDiagonalCodes.alpha.val n] ∧
          (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
            variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
              ![negationWord M (NamedArithmeticUnarySubstitution.value ArithmeticDiagonalCodes.alpha.val n)])) →
        Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map l ≫
          ((SyntacticModel.modelRangeFunctor 𝗣𝗔 M).comparison
            (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)).inv)
          (summand0 (PartialFun.of M) (PartialFun.of M)) =
            setIdem {n : M | (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
              variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
                ![negationWord M (NamedArithmeticUnarySubstitution.value ArithmeticDiagonalCodes.alpha.val n)]} ∧
        Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map l ≫
          ((SyntacticModel.modelRangeFunctor 𝗣𝗔 M).comparison
            (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)).inv)
          (summand1 (PartialFun.of M) (PartialFun.of M)) =
            setIdem {n : M | (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
              variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
                ![NamedArithmeticUnarySubstitution.value ArithmeticDiagonalCodes.alpha.val n]} :=
  printed_diagonal_partial_proof_search Γ

end CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch.PrintedChecks
