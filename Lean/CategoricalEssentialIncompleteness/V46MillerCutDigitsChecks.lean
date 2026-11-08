import CategoricalEssentialIncompleteness.V46MillerCutDigits

namespace CategoricalEssentialIncompleteness.V46.Miller.CutDigits.Checks

example (p : Bits) (n : ℕ) (h : ((rho p) n : ℝ) < 1/2) : p (Nat.pair n 0) = 0 :=
  coordinate_first_zero p n h

example (p : Bits) (n : ℕ) (h : 1/2 < ((rho p) n : ℝ)) : p (Nat.pair n 0) = 1 :=
  coordinate_first_one p n h

example (z : Point) (p : Bits) (hp : p ∈ representations z) :
    {n | (z n : ℝ) < 1/2} ⊆ {n | p (Nat.pair n 0) = 0} ∧
      Disjoint {n | p (Nat.pair n 0) = 0} {n | 1/2 < (z n : ℝ)} :=
  separates_point z p hp

example : ∃ e : ℕ,∀ p : Bits,∀ n,
    OracleProgram.numberedEval e p n = Part.some (1-(p (Nat.pair n 0)).val) ∧
      (1-(p (Nat.pair n 0)).val = 1 ↔ p (Nat.pair n 0) = 0) :=
  uniform_recursive_separator

example (p : Bits) :
    Nat.RecursiveIn (LocalConnectedness.OracleComputation.oracleSet
      (OracleRelative.oracleSupport p))
      (fun n => Part.some (1-(p (Nat.pair n 0)).val)) := decision_recursiveIn p

end CategoricalEssentialIncompleteness.V46.Miller.CutDigits.Checks
