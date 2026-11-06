import CategoricalEssentialIncompleteness.V46ArithmeticNamedOpenTranslation

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedOpenTranslationChecks
open ArithmeticNamedOpenTranslation

example {n : ℕ} (φ : ArithmeticSemisentence n) (seed : ℕ) (bn : Fin n → ℕ) :
    formula seed bn Empty.elim φ = ArithmeticNamedTranslation.translateFormula seed bn φ :=
  formula_empty φ seed bn

example {n : ℕ} (φ : Semiproposition ℒₒᵣ n)
    (seed : ℕ) (bn : Fin n → ℕ) (fn : ℕ → ℕ) :
    formula seed bn fn (Rewriting.shift φ) =
      formula seed bn (fun i => fn (i+1)) φ :=
  formula_shift φ seed bn fn

example {n : ℕ} (φ : Semiproposition ℒₒᵣ (n+1))
    (seed : ℕ) (bn : Fin n → ℕ) (fn : ℕ → ℕ) :
    formula seed bn fn (Rewriting.free φ) =
      formula seed (Fin.snoc bn (fn 0)) (fun i => fn (i+1)) φ :=
  formula_free φ seed bn fn

example (φ : Semiproposition ℒₒᵣ 1) (t : SyntacticTerm ℒₒᵣ)
    (seed : ℕ) (fn : ℕ → ℕ) (hf : ∀ i, fn i < seed) :
    (formula (seed+1) ![seed] fn φ).substitute seed (term ![] fn t) =
      some (formula (seed+1) ![] fn (φ/[t])) :=
  instance_substitution φ t seed fn hf

example {ξ : Type} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n)
    (seed : ℕ) (bn : Fin n → ℕ) (fn : ξ → ℕ) (x : ℕ)
    (t : NamedArithmeticSignature.Term)
    (ht : ∀ z, z ∈ t.freeVariables → z < seed) :
    (formula seed bn fn φ).FreeFor x t :=
  formula_freeFor_bounded φ seed bn fn x t ht

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedOpenTranslationChecks
