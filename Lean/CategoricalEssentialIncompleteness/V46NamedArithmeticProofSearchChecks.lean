import CategoricalEssentialIncompleteness.V46NamedArithmeticProofSearch

/-! # Raw statement checks for the actual arithmetic partial lift -/
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

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch.StatementChecks

example (Γ : Carrier) (φ : Formula) :
    ∃ l : omegaObject 𝗣𝗔 ⟶ coprod (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔),
      ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔],
        (∀ n : M, ¬((positive Γ φ).val.Evalb ![n] ∧ (negative Γ φ).val.Evalb ![n])) →
        Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map l)
          (summand0 (PartialFun.of M) (PartialFun.of M)) =
            setIdem {n : M | (negative Γ φ).val.Evalb ![n]} ∧
        Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map l)
          (summand1 (PartialFun.of M) (PartialFun.of M)) =
            setIdem {n : M | (positive Γ φ).val.Evalb ![n]} :=
  partial_proof_search Γ φ

example (Γ : Carrier) (φ : Formula) (M : Type)
    [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (hd : ∀ n : M, ¬((positive Γ φ).val.Evalb ![n] ∧ (negative Γ φ).val.Evalb ![n]))
    (x y : M) :
    y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (numericalEll Γ φ) x ↔
      ((positive Γ φ).val.Evalb ![x] ∧ y = 2 * x + 1) ∨
        ((negative Γ φ).val.Evalb ![x] ∧ y = 2 * x) :=
  mem_numericalEll M Γ φ hd x y

end CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch.StatementChecks
