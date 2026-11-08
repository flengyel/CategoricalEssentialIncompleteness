import CategoricalEssentialIncompleteness.V46MillerCutSeparatingProgram
noncomputable section
open CategoricalEssentialIncompleteness.V46.Miller

example : ∃d:ℕ,∀p:Bits,∀e k:ℕ,∃i:ℕ,
    i∈OracleProgram.numberedEval d p (Nat.pair e k) ∧
      |(Rationals.q i:ℝ)-Cut.separatingReal e (rho p)|<((2:ℝ)^k)⁻¹ :=
  Cut.separatingReal_program

example : Primrec₂ Cut.SeparatingProgram.use := Cut.SeparatingProgram.use_primrec
example : Primrec (fun a:Word×(ℕ×ℕ) => Cut.SeparatingProgram.index a.1 a.2.1 a.2.2) :=
  Cut.SeparatingProgram.index_primrec

example (p:Bits) (N e k:ℕ) (hN:Cut.SeparatingProgram.use e k≤N) :
    |(Rationals.q (Cut.SeparatingProgram.index (bitPrefix p N) e k):ℝ)-
      Cut.separatingReal e (rho p)|<((2:ℝ)^k)⁻¹ :=
  Cut.SeparatingProgram.index_error p N e k hN
