import CategoricalEssentialIncompleteness.V46NumericalArithmeticProofComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.ProofComparison.Checks
open Coordinates
example (Γ : Carrier) : SentenceProofCodes.allProofs Γ ≅ numericalInterpretation.obj (ProofWords.allProofs Γ) := fullIso Γ
example (Γ : Carrier) : SentenceProofCodes.object Γ ≅
    numericalInterpretation.obj (ArithmeticLiteralModel.proofObject Γ) := rho Γ
example (Γ : Carrier) : (rho Γ).hom ≫ numericalInterpretation.map (ArithmeticLiteralModel.conclusion Γ) =
    SentenceProofCodes.conclusion Γ ≫ literalSentence := rho_conclusion Γ
example (Γ : Carrier) :
    (wordIso Γ).hom ≫ ProofImage.conclusion Γ = conclusion Γ := wordIso_conclusion Γ
example (Γ : Carrier) : StrongEpiMonoFactorisation (conclusion Γ) := imageFactorisation Γ
example (Γ : Carrier) : IsImage (imageFactorisation Γ).toMonoFactorisation := isImage Γ
example (Γ : Carrier) (s : NumericalTuples.Point ProofImage.sentenceObject) :
    (∃ p : NumericalTuples.Point (SentenceProofCodes.object Γ), (conclusion Γ).toFun p = s) ↔
      (ArithmeticLiteralModel.theoremPredicate Γ).val.Evalb (M := ℕ) ![s.val] := fixed_provability Γ s
example (Γ : Carrier) (p : NumericalTuples.Point (SentenceProofCodes.object Γ)) :
    canonicalComparison.hom.app ArithmeticLiteralModel.sentencePredicate ((conclusion Γ).toFun p) =
      (PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map
        ((realization 𝗣𝗔).map (ArithmeticLiteralModel.conclusion Γ))
        ((canonicalRho Γ).hom p) := canonical_conclusion Γ p
example (Γ : Carrier) :
    ∃ r : ℕ → Part ℕ, Partrec r ∧
      ∀ p : NumericalTuples.Point (SentenceProofCodes.object Γ),
        r p.val = Part.some ((canonicalRho Γ).hom p).val.val := canonical_forward_program Γ
example (Γ : Carrier) :
    ∃ r : ℕ → Part ℕ, Partrec r ∧
      ∀ p : PredicateInterpretation.CanonicalDomain 𝗣𝗔 ℕ
        ((realization 𝗣𝗔).obj (ArithmeticLiteralModel.proofObject Γ)),
        r p.val.val = Part.some ((canonicalRho Γ).inv p).val := canonical_backward_program Γ
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.ProofComparison.Checks
