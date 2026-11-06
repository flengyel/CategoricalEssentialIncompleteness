import CategoricalEssentialIncompleteness.V46NamedArithmeticDiagonalLiteralTotal
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates NamedArithmeticSignature
example : ArithmeticOmegaComparison.identityOmega 𝗣𝗔 ⟶ NamedArithmeticLiteralTotal.literalSentence :=
  NamedArithmeticDiagonalLiteralTotal.theta
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (n : M) :
    ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 M).map NamedArithmeticDiagonalLiteralTotal.theta
      (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 M n)).val.val =
        NamedArithmeticUnarySubstitution.value ArithmeticDiagonalCodes.alpha.val n :=
  NamedArithmeticDiagonalLiteralTotal.canonical_value_at M n
example (n : ℕ) :
    ∃ out : Formula,
      (NamedArithmeticUnarySubstitution.namedFormula ArithmeticDiagonalCodes.alpha.val).substitute 0 (numeral n) = some out ∧
        ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map NamedArithmeticDiagonalLiteralTotal.theta
          (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 ℕ n)).val.val =
            NamedArithmeticSignature.formulaCode out ∧ out.freeVariables = [] :=
  NamedArithmeticDiagonalLiteralTotal.standard_literal_result n
