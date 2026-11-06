import CategoricalEssentialIncompleteness.V46ArithmeticNamedFormulaTranslation

noncomputable section
universe w
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedFormulaTranslationChecks
open NamedArithmeticSignature ArithmeticNamedTranslation
variable {K : Type w} [ORingStructure K]

example {n : ℕ} (φ : ArithmeticSemisentence n) (next : ℕ)
    (names : Fin n → ℕ) (h : ∀ i, names i < next) (ρ : ℕ → K) :
    (translateFormula next names φ).Holds functions relations ρ ↔
      φ.Evalb (s := Arithmetic.standardModel K) (fun i => ρ (names i)) :=
  holds_translateFormula φ next names h ρ

example (φ : ArithmeticSemisentence 1) (ρ : ℕ → K) :
    (translateFormula 1 ![0] φ).Holds functions relations ρ ↔ φ.Evalb (s := Arithmetic.standardModel K) ![ρ 0] := by
  have he := holds_translateFormula φ 1 ![0]
    (by intro i; fin_cases i; decide) ρ
  have hv : (fun i : Fin 1 => ρ (![0] i)) = ![ρ 0] := by
    funext i
    fin_cases i
    rfl
  simpa only [hv] using he

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedFormulaTranslationChecks
