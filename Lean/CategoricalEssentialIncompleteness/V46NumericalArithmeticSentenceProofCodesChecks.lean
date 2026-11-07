import CategoricalEssentialIncompleteness.V46NumericalArithmeticSentenceProofCodes
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SentenceProofCodes.Checks
open Coordinates
example (Γ : Carrier) : IsInitial (allAlgebra Γ) := allInitial Γ
example (Γ : Carrier) : (object Γ).dimension = 1 := dimension Γ
example (Γ : Carrier) :
    IsPullback (inclusion Γ) (conclusion Γ) (allConclusion Γ) numericalSyntax.sentenceInclusion := isPullback Γ
example (Γ : Carrier) (p : ℕ) : (object Γ).support p ↔
    ∃ q : NumericalTuples.Point (allProofs Γ), q.val = p ∧
      ∃ s : NumericalTuples.Point numericalSyntax.sentenceObject,
        numericalSyntax.sentenceInclusion.toFun s = (allConclusion Γ).toFun q := membership Γ p
example (Γ : Carrier) : imageSubobject (conclusion Γ) =
    (Subobject.pullback numericalSyntax.sentenceInclusion).obj (imageSubobject (allConclusion Γ)) :=
  generated_sentence_image Γ
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SentenceProofCodes.Checks
