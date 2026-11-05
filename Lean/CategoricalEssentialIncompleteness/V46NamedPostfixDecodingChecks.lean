import CategoricalEssentialIncompleteness.V46NamedPostfixDecoding

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.NamedPostfixDecodingChecks
open NamedPostfixEncoding
variable (σ π : ℕ → Carrier) (d : ℕ)
example :
    (∀ word : ℕ, (Postfix.carrier false (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![word] →
      ∃ r : NamedFiniteSyntax.Term (Symbols σ) d, termCode r = word) ∧
    (∀ word : ℕ, (Postfix.carrier true (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![word] →
      ∃ φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d, formulaCode φ = word) :=
  standard_codes_surjective σ π d
end CategoricalEssentialIncompleteness.V46.NamedPostfixDecodingChecks
