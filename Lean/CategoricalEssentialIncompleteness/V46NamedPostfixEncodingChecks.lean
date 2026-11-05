import CategoricalEssentialIncompleteness.V46NamedPostfixEncoding

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.NamedPostfixEncodingChecks
open NamedPostfixEncoding
variable (σ π : ℕ → Carrier) (d : ℕ)
example (r : NamedFiniteSyntax.Term (Symbols σ) d) :
    (Postfix.carrier false (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![termCode r] :=
  termCode_member π r
example (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    (Postfix.carrier true (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![formulaCode φ] :=
  formulaCode_member φ
example (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    formulaCode φ = Coding.constructor true (formulaPolynomial π d) (formulaInput φ) :=
  formulaCode_root φ
end CategoricalEssentialIncompleteness.V46.NamedPostfixEncodingChecks
