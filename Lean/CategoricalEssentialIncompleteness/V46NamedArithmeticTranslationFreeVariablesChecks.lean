import CategoricalEssentialIncompleteness.V46NamedArithmeticTranslationFreeVariables
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.ArithmeticNamedTranslation
example {n : ℕ} (next : ℕ) (names : Fin n → ℕ) (φ : ArithmeticSemisentence n) (x : ℕ)
    (hx : x ∈ (translateFormula next names φ).freeVariables) : ∃ i, names i = x :=
  translateFormula_freeVariables φ next names x hx
example (α : ArithmeticSemisentence 1) (x : ℕ)
    (hx : x ∈ (translateFormula 1 ![0] α).freeVariables) : x = 0 := translateUnary_freeVariables α x hx
