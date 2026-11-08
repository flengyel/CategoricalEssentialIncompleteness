import CategoricalEssentialIncompleteness.V46MillerUnanimity
noncomputable section
namespace CategoricalEssentialIncompleteness.V46.Miller.Unanimity.Checks
example : ∃ d : ℕ, ∀ z : ℕ → Set.Icc (0 : ℝ) 1,
    ∀ p : ℕ → Fin 2, rho p = z → ∀ e n : ℕ,
      OracleProgram.numberedEval d p (Nat.pair e n) = tau z e n := printed_unanimity
example (z : ℕ → Set.Icc (0 : ℝ) 1) (p : ℕ → Fin 2) (hp : rho p = z) (e n m : ℕ) :
    m ∈ OracleProgram.numberedEval unanimityIndex p (Nat.pair e n) ↔
      ∀ q : ℕ → Fin 2, rho q = z → m ∈ OracleProgram.numberedEval e q n :=
  unanimityIndex_graph z p hp e n m
example (z : ℕ → Set.Icc (0 : ℝ) 1) (p : ℕ → Fin 2) (hp : rho p = z) (e n : ℕ) :
    (OracleProgram.numberedEval unanimityIndex p (Nat.pair e n)).Dom ↔
      ∃ m : ℕ, ∀ q : ℕ → Fin 2, rho q = z → m ∈ OracleProgram.numberedEval e q n :=
  unanimityIndex_domain z p hp e n
example (z : ℕ → Set.Icc (0 : ℝ) 1) (p q : ℕ → Fin 2)
    (hp : rho p = z) (hq : rho q = z) (e n : ℕ) :
    OracleProgram.numberedEval unanimityIndex p (Nat.pair e n) =
      OracleProgram.numberedEval unanimityIndex q (Nat.pair e n) := representation_independent z p q hp hq e n
example (z : ℕ → Set.Icc (0 : ℝ) 1) (e n m : ℕ) :
    m ∈ tau z e n ↔ ∀ q : ℕ → Fin 2, rho q = z → m ∈ OracleProgram.numberedEval e q n := tau_graph z e n m
end CategoricalEssentialIncompleteness.V46.Miller.Unanimity.Checks
