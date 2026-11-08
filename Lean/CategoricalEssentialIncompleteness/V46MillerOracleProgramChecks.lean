import CategoricalEssentialIncompleteness.V46MillerOracleProgram
noncomputable section
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.Miller.OracleProgram

example (e : Nat.Partrec.Code) (p : Bits) (n y : ℕ) :
    y ∈ eval e p n ↔ ∃ k,
      y ∈ finiteEval e ((bitPrefix p k).map Fin.val) n := eval_graph e p n y

example (e : Nat.Partrec.Code) (p : Bits) (n : ℕ) :
    (eval e p n).Dom ↔ ∃ k,
      (finiteEval e ((bitPrefix p k).map Fin.val) n).Dom := eval_domain e p n

example (e : Nat.Partrec.Code) (l l' : List ℕ) (h : l <+: l') (n y z : ℕ)
    (hy : y ∈ finiteEval e l n) (hz : z ∈ finiteEval e l' n) : y=z :=
  finiteEval_compatible e l l' h n y z hy hz
