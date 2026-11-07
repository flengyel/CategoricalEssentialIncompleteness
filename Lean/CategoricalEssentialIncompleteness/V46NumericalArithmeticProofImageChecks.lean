import CategoricalEssentialIncompleteness.V46NumericalArithmeticProofImage
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.ProofImage.Checks
example (Γ : Carrier) : IsImage (imageFactorisation Γ).toMonoFactorisation := isImage Γ
example (Γ : Carrier) : quotient Γ ≫ inclusion Γ = conclusion Γ := factor Γ
example (Γ : Carrier) (s : NumericalTuples.Point sentenceObject) :
    (∃ p : NumericalTuples.Point (proofObject Γ), (conclusion Γ).toFun p = s) ↔
      (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
        NamedArithmeticSignature.variableSymbols NamedArithmeticSignature.functionSymbols
        NamedArithmeticSignature.relationSymbols NamedArithmeticSignature.bound Γ).val.Evalb (M := ℕ) ![s.val] :=
  image_membership Γ s
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.ProofImage.Checks
