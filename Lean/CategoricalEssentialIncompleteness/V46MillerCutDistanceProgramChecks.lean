import CategoricalEssentialIncompleteness.V46MillerCutDistanceProgram
noncomputable section
open Encodable
open CategoricalEssentialIncompleteness.V46.Miller

example : ∃d:ℕ,∀p:Bits,∀e m t k:ℕ,∃i:ℕ,
    i∈OracleProgram.numberedEval d p (encode ((e,m),(t,k))) ∧
      |(Rationals.q i:ℝ)-Cut.Distance.delta e m t (rho p)|<((2:ℝ)^k)⁻¹ :=
  Cut.Distance.exists_distance_program

example (p:Bits) (N e m t k:ℕ) (hN:Cut.Distance.use e m t k≤N) :
    |(Rationals.q (Cut.Distance.finiteIndex (bitPrefix p N) ((e,m),(t,k))):ℝ)-
      Cut.Distance.delta e m t (rho p)|≤((2:ℝ)^(k+2))⁻¹ :=
  Cut.Distance.finiteIndex_error p N e m t k hN
