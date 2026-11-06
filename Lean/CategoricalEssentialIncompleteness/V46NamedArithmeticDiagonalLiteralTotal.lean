import CategoricalEssentialIncompleteness.V46NamedArithmeticLiteralTotal
import CategoricalEssentialIncompleteness.V46NamedArithmeticUnarySubstitution
import CategoricalEssentialIncompleteness.V46ArithmeticDiagonalCodes

/-! Exact diagonal specialization of the generic literal-Total sentence
map. All proofs are applications of generic theorems; the selected index
inside ArithmeticDiagonalCodes.alpha is never normalized. -/
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalLiteralTotal
open NamedArithmeticSignature

 def theta : ArithmeticOmegaComparison.identityOmega 𝗣𝗔 ⟶ NamedArithmeticLiteralTotal.literalSentence :=
  NamedArithmeticLiteralTotal.theta
    (NamedArithmeticUnarySubstitution.namedFormula ArithmeticDiagonalCodes.alpha.val)
    (NamedArithmeticUnarySubstitution.namedFormula_freeVariables ArithmeticDiagonalCodes.alpha.val)

 theorem canonical_value_at
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (n : M) :
    ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 M).map theta
      (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 M n)).val.val =
        NamedArithmeticUnarySubstitution.value ArithmeticDiagonalCodes.alpha.val n :=
  NamedArithmeticLiteralTotal.canonical_value_at
    (NamedArithmeticUnarySubstitution.namedFormula ArithmeticDiagonalCodes.alpha.val)
    (NamedArithmeticUnarySubstitution.namedFormula_freeVariables ArithmeticDiagonalCodes.alpha.val) M n

 theorem standard_literal_result (n : ℕ) :
    ∃ out : Formula,
      (NamedArithmeticUnarySubstitution.namedFormula ArithmeticDiagonalCodes.alpha.val).substitute 0 (numeral n) = some out ∧
        ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map theta
          (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 ℕ n)).val.val =
            NamedArithmeticSignature.formulaCode out ∧ out.freeVariables = [] :=
  NamedArithmeticLiteralTotal.standard_literal_result
    (NamedArithmeticUnarySubstitution.namedFormula ArithmeticDiagonalCodes.alpha.val)
    (NamedArithmeticUnarySubstitution.namedFormula_freeVariables ArithmeticDiagonalCodes.alpha.val) n

end CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalLiteralTotal
