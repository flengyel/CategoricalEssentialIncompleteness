import CategoricalEssentialIncompleteness.V46NamedPostfixSubstitution

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NamedPostfixSubstitutionChecks
open NamedPostfixEncoding ConcreteNamedSubstitution SyntacticSyntax.NatVectors
variable (σ π : ℕ → Carrier) (d : ℕ)
example (r t : NamedFiniteSyntax.Term (Symbols σ) d) (x : ℕ) :
    substitutionResult variableCarrier σ π d x (termCode t) (termCode r) =
      termCode (r.substitute x t) := substitutionResult_termCode π r t x
example (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d)
    (t : NamedFiniteSyntax.Term (Symbols σ) d) (x : ℕ) :
    substitutionResult variableCarrier σ π d x (termCode t) (formulaCode φ) =
      optionCode (φ.substitute x t) := substitutionResult_formulaCode φ t x
example (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d)
    (t : NamedFiniteSyntax.Term (Symbols σ) d) (x : ℕ) :
    substitutionFreeFor variableCarrier σ π d x (termCode t) (formulaCode φ) = 1 ↔
      φ.FreeFor x t := substitutionFreeFor_formulaCode φ t x
/-- The original whole quantified formula is returned without a
recursive body-success assumption. -/
example (body : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d)
    (t : NamedFiniteSyntax.Term (Symbols σ) d) (x : ℕ) :
    substitutionResult variableCarrier σ π d x (termCode t) (formulaCode (.all x body)) =
      optionCode (some (.all x body)) := by
  rw [substitutionResult_formulaCode]
  simp [NamedFiniteSyntax.Formula.substitute]
end CategoricalEssentialIncompleteness.V46.NamedPostfixSubstitutionChecks
