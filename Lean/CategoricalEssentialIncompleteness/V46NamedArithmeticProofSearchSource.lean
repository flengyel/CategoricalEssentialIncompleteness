/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticProofSearchPredicates
public import CategoricalEssentialIncompleteness.V46NamedArithmeticProofSearchRefutations
public import CategoricalEssentialIncompleteness.V46ArithmeticOmegaComparison

/-! # Source equalities for the actual arithmetic theorem/refutation pullbacks

The raw source program is that of the constructed fixed-formula morphism.
The two inverse-image predicates are identified by universal PA graph
equality before interpreting any particular model.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open FailureOfComposition.ProofSearch FailureOfComposition.UniformIndexQuotient
open FailureOfComposition.TypedNearProduct
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch

open NamedArithmeticSignature

/-- The source program is obtained from the actual graph morphism, rather
than selected from a standard extensional equality. -/
def sourceTheta (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔 :=
  omegaArrow 𝗣𝗔 (NamedArithmeticFixedSubstitution.morphism φ hφ).programClass

theorem sourceTheta_total (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    isTotal (sourceTheta φ hφ) := by
  change rst (sourceTheta φ hφ) = 𝟙 (omegaObject 𝗣𝗔)
  apply CodedHom.ext
  rw [restriction_val]
  change domainClass 𝗣𝗔 (NamedArithmeticFixedSubstitution.morphism φ hφ).programClass =
    objectIdempotent 𝗣𝗔 .omega
  have h := congrArg (fun e : Idem (omegaObject 𝗣𝗔) => e.hom.val)
    (ArithmeticOmegaComparison.variables_idempotent 𝗣𝗔)
  change predicateClass 𝗣𝗔 variableSymbols = objectIdempotent 𝗣𝗔 .omega at h
  exact (NamedArithmeticFixedSubstitution.morphism φ hφ).programClass_domain.trans h

theorem positive_source_pull (Γ : Carrier) (φ : Formula)
    (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    Idem.pull (sourceTheta φ hφ)
      (predicateIdem 𝗣𝗔 (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound Γ)) =
      predicateIdem 𝗣𝗔 (positive Γ φ) := by
  unfold sourceTheta
  rw [graphPullCarrier_idem]
  apply Idem.ext
  apply CodedHom.ext
  change predicateClass 𝗣𝗔 (graphPullCarrier 𝗣𝗔 (NamedArithmeticFixedSubstitution.morphism φ hφ)
    (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
      variableSymbols functionSymbols relationSymbols bound Γ)) = predicateClass 𝗣𝗔 (positive Γ φ)
  apply programClass_ext 𝗣𝗔
  intro M _ _ x y
  simp only [predicateClass_model,graphPullCarrier_eval,
    NamedArithmeticFixedSubstitution.morphism_graph_eval,positive_eval,exists_eq_left]

theorem negative_source_pull (Γ : Carrier) (φ : Formula)
    (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    Idem.pull (sourceTheta φ hφ)
      (predicateIdem 𝗣𝗔 (SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound Γ)) =
      predicateIdem 𝗣𝗔 (negative Γ φ) := by
  unfold sourceTheta
  rw [graphPullCarrier_idem]
  apply Idem.ext
  apply CodedHom.ext
  change predicateClass 𝗣𝗔 (graphPullCarrier 𝗣𝗔 (NamedArithmeticFixedSubstitution.morphism φ hφ)
    (SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔
      variableSymbols functionSymbols relationSymbols bound Γ)) = predicateClass 𝗣𝗔 (negative Γ φ)
  apply programClass_ext 𝗣𝗔
  intro M _ _ x y
  simp only [predicateClass_model,graphPullCarrier_eval,
    NamedArithmeticFixedSubstitution.morphism_graph_eval,
    negative_literal_refutation M Γ φ hφ,exists_eq_left]

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem sourceTheta_graph (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0)
    (x y : M) :
    y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (sourceTheta φ hφ) x ↔
      y = NamedArithmeticFixedSubstitution.value φ x := by
  exact (SyntacticModel.mem_model 𝗣𝗔 M (sourceTheta φ hφ) x y).trans
    ((SyntacticModel.mem_arrow 𝗣𝗔 M (sourceTheta φ hφ) _ _).trans
      (((NamedArithmeticFixedSubstitution.morphism φ hφ).programClass_model M x y).trans
        (NamedArithmeticFixedSubstitution.morphism_graph_eval (M := M) φ hφ x y)))

/-- The interpreted source pullback is exactly the positive evidence set,
including at all nonstandard elements of the model. -/
theorem positive_source_pull_model (Γ : Carrier) (φ : Formula)
    (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
      (Idem.pull (sourceTheta φ hφ)
        (predicateIdem 𝗣𝗔 (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
          variableSymbols functionSymbols relationSymbols bound Γ))) =
      setIdem {n : M | (positive Γ φ).val.Evalb ![n]} := by
  rw [positive_source_pull]
  exact model_predicateIdem 𝗣𝗔 (positive Γ φ) M

theorem negative_source_pull_model (Γ : Carrier) (φ : Formula)
    (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
      (Idem.pull (sourceTheta φ hφ)
        (predicateIdem 𝗣𝗔 (SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔
          variableSymbols functionSymbols relationSymbols bound Γ))) =
      setIdem {n : M | (negative Γ φ).val.Evalb ![n]} := by
  rw [negative_source_pull]
  exact model_predicateIdem 𝗣𝗔 (negative Γ φ) M

/-- The lift's fibers are the interpretations of the actual source
theorem/refutation inverse-image idempotents. -/
theorem ell_source_fibers (Γ : Carrier) (φ : Formula)
    (hφ : ∀ y, y ∈ φ.freeVariables → y = 0)
    (hd : ∀ n : M, ¬((positive Γ φ).val.Evalb ![n] ∧ (negative Γ φ).val.Evalb ![n])) :
    Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map (ell Γ φ))
      (summand0 (PartialFun.of M) (PartialFun.of M)) =
        (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
          (Idem.pull (sourceTheta φ hφ)
            (predicateIdem 𝗣𝗔 (SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔
              variableSymbols functionSymbols relationSymbols bound Γ))) ∧
    Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map (ell Γ φ))
      (summand1 (PartialFun.of M) (PartialFun.of M)) =
        (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
          (Idem.pull (sourceTheta φ hφ)
            (predicateIdem 𝗣𝗔 (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
              variableSymbols functionSymbols relationSymbols bound Γ))) := by
  exact ⟨(pull_summand0 M Γ φ hd).trans (negative_source_pull_model M Γ φ hφ).symm,
    (pull_summand1 M Γ φ hd).trans (positive_source_pull_model M Γ φ hφ).symm⟩

end Models

end CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch
