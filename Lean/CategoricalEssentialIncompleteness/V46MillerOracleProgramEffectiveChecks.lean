import CategoricalEssentialIncompleteness.V46MillerOracleProgramEffective
noncomputable section
open Encodable
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.Miller.OracleProgram

example : Partrec (fun a : (Nat.Partrec.Code × List ℕ) × ℕ => finiteEval a.1.1 a.1.2 a.2) :=
  finiteEval_partrec
example : REPred HaltingCylinder := haltingCylinder_re
example (e : Nat.Partrec.Code) (p : Bits) (n y : ℕ) :
    y ∈ eval e p n ↔ ∃ s : Word, HaltingCylinder (((e,n),y),s) ∧ p ∈ cylinder s :=
  eval_cylinders e p n y
example : Computable₂ sectionCode := sectionCode_computable
example (e : Nat.Partrec.Code) (p : Bits) (x n : ℕ) :
    eval (sectionCode e x) p n = eval e p (Nat.pair x n) := sectionCode_eval e x p n
example (e : Nat.Partrec.Code) (p : Bits) (n : ℕ) :
    eval universalCode p (Nat.pair (encode e) n) = eval e p n := universalCode_eval e p n
example (e : Nat.Partrec.Code) (p : Bits) (n : ℕ) :
    eval (ordinaryCode e) p n = e.eval n := ordinaryCode_eval e p n
