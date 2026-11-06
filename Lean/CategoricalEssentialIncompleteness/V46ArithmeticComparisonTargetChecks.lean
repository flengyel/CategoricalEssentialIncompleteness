/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ArithmeticComparisonTarget
import CategoricalEssentialIncompleteness.V46NamedArithmeticProofSearchPrinted
import CategoricalEssentialIncompleteness.V46ArithmeticDiagonalCodesTuring

/-! # The categorical comparison on the actual arithmetic sentence carrier

This internal assembly lemma is used after deriving its bounds and consistency
from the concrete Gamma hypotheses. Its target is the literal sentence object,
not the ambient numerical carrier.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.CoprodStruct
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.ArithmeticComparisonTarget.Checks
open NamedArithmeticSignature ArithmeticLiteralModel

variable (Γ : Carrier) (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example
    (hΓ : ∀ s : Obj 𝗣𝗔 M sentencePredicate,
      ¬ ((theoremPredicate Γ).val.Evalb ![s.val] ∧
        (theoremPredicate Γ).val.Evalb ![NamedArithmeticProofSearch.negationWord M s.val]))
    (hzero : ∀ n : M, ArithmeticDiagonalCodes.alpha.val.Evalb ![n] →
      (NamedArithmeticProofSearch.positive Γ diagonalFormula).val.Evalb ![n])
    (hone : ∀ n : M, ArithmeticDiagonalCodes.beta.val.Evalb ![n] →
      (NamedArithmeticProofSearch.negative Γ diagonalFormula).val.Evalb ![n]) :
    ∃ g : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔, isTotal g ∧
      Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map g ≫
        ArithmeticLiteralCoordinates.thetaMap M diagonalFormula diagonalFormula_freeVariables) (ArithmeticLiteralCoordinates.theory M Γ) = ⊥ ∧
      Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map g ≫
        ArithmeticLiteralCoordinates.thetaMap M diagonalFormula diagonalFormula_freeVariables)
        (Idem.pull (ArithmeticLiteralCoordinates.negationMap M) (ArithmeticLiteralCoordinates.theory M Γ)) = ⊥ ∧
      ArithmeticLiteralCoordinates.theory M Γ ⊔ Idem.pull (ArithmeticLiteralCoordinates.negationMap M) (ArithmeticLiteralCoordinates.theory M Γ) ≠ ⊤ :=
  comparison_of_evidence_bounds Γ M hΓ hzero hone

end CategoricalEssentialIncompleteness.V46.ArithmeticComparisonTarget.Checks
