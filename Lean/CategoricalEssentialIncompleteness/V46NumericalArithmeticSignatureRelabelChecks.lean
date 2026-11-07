import CategoricalEssentialIncompleteness.V46NumericalArithmeticSignatureRelabel
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SignatureRelabel.Checks
open NamedFiniteSyntax NamedPostfixEncoding
variable {σ τ π ρ : ℕ → Carrier} {d : ℕ}
variable (h : ∀ (k n : ℕ), (σ k).val.Evalb ![n] ↔ (τ k).val.Evalb ![n])
  (j : ∀ (k n : ℕ), (π k).val.Evalb ![n] ↔ (ρ k).val.Evalb ![n])
example (r : Term (Symbols σ) d) : termCode (term h r) = termCode r := term_code h r
example (φ : Formula (Symbols σ) (Symbols π) d) :
    formulaCode (formula h j φ) = formulaCode φ := formula_code h j φ
example (φ : Formula (Symbols σ) (Symbols π) d) (x : ℕ) (t : Term (Symbols σ) d) :
    Option.map (formula h j) (φ.substitute x t) =
      (formula h j φ).substitute x (term h t) := formula_substitute h j φ x t
example (Γ : Carrier) (φ : Formula (Symbols σ) (Symbols π) d) :
    SyntacticNamedHilbert.Derives τ ρ d Γ (formula h j φ) ↔
      SyntacticNamedHilbert.Derives σ π d Γ φ := derives_iff h j Γ φ
example (x : ℕ) (φ : Formula (Symbols σ) (Symbols π) d) (t : Term (Symbols σ) d) :
    Option.map (formula h j) ((Formula.all x φ).substitute x t) =
      some (Formula.all x (formula h j φ)) := by
  simp [Formula.substitute,formula]
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SignatureRelabel.Checks
