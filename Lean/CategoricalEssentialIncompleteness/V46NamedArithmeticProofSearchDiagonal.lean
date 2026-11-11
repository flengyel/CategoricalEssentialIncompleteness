/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticProofSearchRefutations
public import CategoricalEssentialIncompleteness.V46NamedArithmeticUnarySubstitution
public import CategoricalEssentialIncompleteness.V46ArithmeticDiagonalCodes

/-! # Lemma 7.2 at the printed diagonal formula

The specialization is by theorem application, so the selected diagonal
program index remains opaque. The input predicates are the actual generated
Γ theorem/refutation images after the proved fixed-formula numeral map.
-/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.CoprodStruct
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch

open NamedArithmeticSignature

def diagonalPositive (Γ : Carrier) : Carrier :=
  positive Γ (NamedArithmeticUnarySubstitution.namedFormula ArithmeticDiagonalCodes.alpha.val)

def diagonalNegative (Γ : Carrier) : Carrier :=
  negative Γ (NamedArithmeticUnarySubstitution.namedFormula ArithmeticDiagonalCodes.alpha.val)

def diagonalEll (Γ : Carrier) :
    omegaObject 𝗣𝗔 ⟶ coprod (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔) :=
  ell Γ (NamedArithmeticUnarySubstitution.namedFormula ArithmeticDiagonalCodes.alpha.val)

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem diagonalPositive_theorem_image (Γ : Carrier) (n : M) :
    (diagonalPositive Γ).val.Evalb ![n] ↔
      (SyntacticGeneratedAxioms.theoremCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
          ![NamedArithmeticUnarySubstitution.value ArithmeticDiagonalCodes.alpha.val n] :=
  positive_theorem_image M Γ
    (NamedArithmeticUnarySubstitution.namedFormula ArithmeticDiagonalCodes.alpha.val) n

theorem diagonalNegative_refutation_image (Γ : Carrier) (n : M) :
    (diagonalNegative Γ).val.Evalb ![n] ↔
      (SyntacticGeneratedAxioms.refutationCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
          ![NamedArithmeticUnarySubstitution.value ArithmeticDiagonalCodes.alpha.val n] :=
  negative_refutation_image M Γ
    (NamedArithmeticUnarySubstitution.namedFormula ArithmeticDiagonalCodes.alpha.val)
    (NamedArithmeticUnarySubstitution.namedFormula_freeVariables ArithmeticDiagonalCodes.alpha.val) n

end Models

/-- The source arrow is chosen before M and before disjointness, and its
fibers are the actual arithmetic Γ theorem/refutation images. -/
theorem diagonal_partial_proof_search (Γ : Carrier) :
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
  actual_partial_proof_search Γ
    (NamedArithmeticUnarySubstitution.namedFormula ArithmeticDiagonalCodes.alpha.val)
    (NamedArithmeticUnarySubstitution.namedFormula_freeVariables ArithmeticDiagonalCodes.alpha.val)

end CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch
