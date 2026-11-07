import CategoricalEssentialIncompleteness.V46NumericalArithmeticPA
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.PAChecks
open NamedArithmeticSignature ArithmeticNamedAxiomComparison

example (Γ : Carrier)
    (hΓ : ∀ word : ℕ, ArithmeticIndexedPAEnumeration.axiomCodes.val.Evalb ![word] → Γ.val.Evalb ![word]) :
    ∀ ψ : Formula, PAAxiom ψ →
      SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound Γ ψ := extendsPA Γ hΓ

example (Γ : Carrier)
    (hΓ : ∀ word : ℕ, ArithmeticIndexedPAEnumeration.axiomCodes.val.Evalb ![word] → Γ.val.Evalb ![word]) :
    ArithmeticNamedProofTranslation.AxiomsAdmissible Γ 𝗣𝗔 := axiomsAdmissible Γ hΓ

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.PAChecks
