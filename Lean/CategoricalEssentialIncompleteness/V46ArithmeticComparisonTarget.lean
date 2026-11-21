/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticLiteralCoordinates
public import CategoricalEssentialIncompleteness.V46NamedArithmeticProofSearchPrinted
public import CategoricalEssentialIncompleteness.V46ArithmeticDiagonalCodesTuring

/-! # The categorical comparison on the arithmetic sentence carrier

This internal assembly lemma is used after deriving its bounds and consistency from
the concrete Gamma hypotheses. Its target is the sentence object, not the ambient
numerical carrier.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.CoprodStruct
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedRecursionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.ArithmeticComparisonTarget
open NamedArithmeticSignature ArithmeticLiteralModel

abbrev diagonalFormula : Formula :=
  NamedArithmeticUnarySubstitution.namedFormula ArithmeticDiagonalCodes.alpha.val

theorem diagonalFormula_freeVariables : ∀ y, y ∈ diagonalFormula.freeVariables → y = 0 :=
  NamedArithmeticUnarySubstitution.namedFormula_freeVariables ArithmeticDiagonalCodes.alpha.val

variable (Γ : Carrier) (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Theorem4.2 is applied to the source Turing morphism and the constructed partial source
lift. No arithmetic incompleteness theorem is used. -/
theorem comparison_of_evidence_bounds
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
      ArithmeticLiteralCoordinates.theory M Γ ⊔ Idem.pull (ArithmeticLiteralCoordinates.negationMap M) (ArithmeticLiteralCoordinates.theory M Γ) ≠ ⊤ := by
  let F := SyntacticModel.modelRangeFunctor 𝗣𝗔 M
  have hU : F.toFunctor.map (𝟙 (omegaObject 𝗣𝗔)) ≠ 0 := by
    rw [F.toFunctor.map_id]
    intro he
    have h := congrFun he (0 : M)
    change Part.some (0 : M) = Part.none at h
    exact Part.notMem_none 0 (h ▸ Part.mem_some 0)
  have hdisjoint : ∀ n : M, ¬(
      (theoremPredicate Γ).val.Evalb ![NamedArithmeticFixedSubstitution.value diagonalFormula n] ∧
      (theoremPredicate Γ).val.Evalb
        ![NamedArithmeticProofSearch.negationWord M
          (NamedArithmeticFixedSubstitution.value diagonalFormula n)]) := by
    intro n
    exact hΓ (thetaPoint M diagonalFormula diagonalFormula_freeVariables n)
  obtain ⟨l,hl⟩ := NamedArithmeticProofSearch.printed_partial_proof_search
    Γ diagonalFormula diagonalFormula_freeVariables
  obtain ⟨hs0,hs1⟩ := hl M hdisjoint
  let s := (SyntacticModel.modelFunctor 𝗣𝗔 M).map l ≫
    (F.comparison (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)).inv
  have hsa : Idem.pull s (summand0 (PartialFun.of M) (PartialFun.of M)) =
      Idem.pull (ArithmeticLiteralCoordinates.thetaMap M diagonalFormula diagonalFormula_freeVariables)
        (Idem.pull (ArithmeticLiteralCoordinates.negationMap M) (ArithmeticLiteralCoordinates.theory M Γ)) := by
    exact hs0.trans ((ArithmeticSetModelLaws.setIdem_congr (fun n =>
      (NamedArithmeticProofSearch.negative_eval_word M Γ diagonalFormula
        diagonalFormula_freeVariables n).symm)).trans
      (ArithmeticLiteralCoordinates.theta_refutation_pull M Γ diagonalFormula
        diagonalFormula_freeVariables).symm)
  have hsb : Idem.pull s (summand1 (PartialFun.of M) (PartialFun.of M)) =
      Idem.pull (ArithmeticLiteralCoordinates.thetaMap M diagonalFormula diagonalFormula_freeVariables) (ArithmeticLiteralCoordinates.theory M Γ) := by
    exact hs1.trans ((ArithmeticSetModelLaws.setIdem_congr (fun n =>
      (NamedArithmeticProofSearch.positive_eval M Γ diagonalFormula n).symm)).trans
      (ArithmeticLiteralCoordinates.theta_theory_pull M Γ diagonalFormula
        diagonalFormula_freeVariables).symm)
  have ha0 : F.mapIdem (diagonal0 ArithmeticDiagonalCodes.sourceTau (omegaCoprodIso 𝗣𝗔).symm) ≤
      Idem.pull (ArithmeticLiteralCoordinates.thetaMap M diagonalFormula diagonalFormula_freeVariables) (ArithmeticLiteralCoordinates.theory M Γ) := by
    exact le_of_eq_of_le (ArithmeticDiagonalCodes.model_a0 M)
      (le_of_le_of_eq (ArithmeticSetModelLaws.setIdem_le hzero)
        (ArithmeticLiteralCoordinates.theta_theory_pull M Γ diagonalFormula
          diagonalFormula_freeVariables).symm)
  have ha1 : F.mapIdem (diagonal1 ArithmeticDiagonalCodes.sourceTau (omegaCoprodIso 𝗣𝗔).symm) ≤
      Idem.pull (ArithmeticLiteralCoordinates.thetaMap M diagonalFormula diagonalFormula_freeVariables)
        (Idem.pull (ArithmeticLiteralCoordinates.negationMap M) (ArithmeticLiteralCoordinates.theory M Γ)) := by
    exact le_of_eq_of_le (ArithmeticDiagonalCodes.model_a1 M)
      (le_of_le_of_eq (ArithmeticSetModelLaws.setIdem_le hone)
        (ArithmeticLiteralCoordinates.theta_refutation_pull M Γ diagonalFormula
          diagonalFormula_freeVariables).symm)
  have hlift : F.toFunctor.map l = s ≫ (F.comparison _ _).hom := by
    dsimp only [s]
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
    rfl
  exact logical_comparison_target F ArithmeticDiagonalCodes.sourceTau
    ArithmeticDiagonalCodes.sourceTau_isTuring (omegaCoprodIso 𝗣𝗔).symm hU
    (ArithmeticLiteralCoordinates.thetaMap M diagonalFormula diagonalFormula_freeVariables)
    (ArithmeticLiteralCoordinates.thetaMap_total M diagonalFormula diagonalFormula_freeVariables)
    (ArithmeticLiteralCoordinates.negationMap M) (ArithmeticLiteralCoordinates.theory M Γ) (ArithmeticLiteralCoordinates.theory_consistent M Γ hΓ)
    ha0 ha1 s hsa hsb l hlift

end CategoricalEssentialIncompleteness.V46.ArithmeticComparisonTarget
