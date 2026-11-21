/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticProofSearchNegation
public import CategoricalEssentialIncompleteness.V46NamedArithmeticProofSearchDiagonal

/-! # The partial Γ proof-search statement

The evidence predicates here are the selected program of the constructed
Γ theory at Θ and its proved primitive-recursive Neg extension. The source
morphism is quantified before every model and every disjointness witness.
-/

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

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch

open NamedArithmeticSignature

/-- The canonical comparison on recursively interpreted sums is the identity, so its
inverse is the identity as well. -/
theorem coproduct_comparison_inv_eq_id (M : Type)
    [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] :
    ((SyntacticModel.modelRangeFunctor 𝗣𝗔 M).comparison
      (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)).inv =
        𝟙 (coprod (PartialFun.of M) (PartialFun.of M)) := by
  have hh : ((SyntacticModel.modelRangeFunctor 𝗣𝗔 M).comparison
      (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)).hom =
        𝟙 (coprod (PartialFun.of M) (PartialFun.of M)) :=
    SyntacticModel.model_comparison_eq_id 𝗣𝗔 M (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)
  have h := ((SyntacticModel.modelRangeFunctor 𝗣𝗔 M).comparison
    (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)).inv_hom_id
  erw [hh,Category.comp_id] at h
  exact h

/-- This is the manuscript's decoded map F(ell) followed by chi inverse,
derived by postcomposition from the proved source-lift comparison. -/
theorem ell_comparison_inv (Γ : Carrier) (φ : Formula) (M : Type)
    [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] :
    (SyntacticModel.modelFunctor 𝗣𝗔 M).map (ell Γ φ) ≫
      ((SyntacticModel.modelRangeFunctor 𝗣𝗔 M).comparison
        (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)).inv =
      (SyntacticModel.modelFunctor 𝗣𝗔 M).map (ell Γ φ) := by
  have h := congrArg (fun f => f ≫
      ((SyntacticModel.modelRangeFunctor 𝗣𝗔 M).comparison
        (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)).inv)
    (ell_comparison M Γ φ)
  simpa only [Category.assoc,Iso.hom_inv_id,Category.comp_id] using h

/-- The complete fibers, using the selected Γ program and the constructed numerical Θ and
Neg graphs, for a fixed unary formula. -/
theorem printed_partial_proof_search (Γ : Carrier) (φ : Formula)
    (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
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
                ![NamedArithmeticFixedSubstitution.value φ n]} := by
  obtain ⟨l,hl⟩ := partial_proof_search Γ φ
  refine ⟨l,fun M _ _ hd => ?_⟩
  have hdisjoint : ∀ n : M, ¬((positive Γ φ).val.Evalb ![n] ∧ (negative Γ φ).val.Evalb ![n]) := by
    intro n hn
    exact hd n ⟨(positive_eval M Γ φ n).mp hn.1,
      (negative_eval_word M Γ φ hφ n).mp hn.2⟩
  obtain ⟨hzero,hone⟩ := hl M hdisjoint
  constructor
  · erw [coproduct_comparison_inv_eq_id M,Category.comp_id]
    simpa only [negative_eval_word M Γ φ hφ] using hzero
  · erw [coproduct_comparison_inv_eq_id M,Category.comp_id]
    simpa only [positive_eval M Γ φ] using hone

/-- Lemma 8.2 for the diagonal formula. The source lift is chosen before M; the hypothesis
is only disjointness in that model. -/
theorem printed_diagonal_partial_proof_search (Γ : Carrier) :
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
  printed_partial_proof_search Γ
    (NamedArithmeticUnarySubstitution.namedFormula ArithmeticDiagonalCodes.alpha.val)
    (NamedArithmeticUnarySubstitution.namedFormula_freeVariables ArithmeticDiagonalCodes.alpha.val)

end CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch
