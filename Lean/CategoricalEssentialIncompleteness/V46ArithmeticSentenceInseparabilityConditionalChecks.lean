import CategoricalEssentialIncompleteness.V46ArithmeticSentenceInseparabilityConditional
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.CoprodStruct
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
namespace CategoricalEssentialIncompleteness.V46.ArithmeticSentenceInseparabilityConditionalChecks
open ArithmeticSentenceInseparability
example (C : Set ℕ) (hC : ComputablePred (· ∈ C)) :
    ∃ (s : PartialFun.of ℕ ⟶ coprod (PartialFun.of ℕ) (PartialFun.of ℕ)) (q : ℕ),
      isTotal s ∧
      Idem.pull s (summand0 (PartialFun.of ℕ) (PartialFun.of ℕ)) = setIdem Cᶜ ∧
      Idem.pull s (summand1 (PartialFun.of ℕ) (PartialFun.of ℕ)) = setIdem C ∧
      (SyntacticModel.modelFunctor 𝗣𝗔 ℕ).map
        (arrowOfIndex 𝗣𝗔 .omega (.coproduct .omega .omega) q) =
      s ≫ ((SyntacticModel.modelRangeFunctor 𝗣𝗔 ℕ).comparison
        (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)).hom :=
  recursive_set_conditional C hC
end CategoricalEssentialIncompleteness.V46.ArithmeticSentenceInseparabilityConditionalChecks
