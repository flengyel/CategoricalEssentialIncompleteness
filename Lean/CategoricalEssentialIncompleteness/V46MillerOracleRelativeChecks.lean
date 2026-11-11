/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerOracleRelative


/-! # Statement checks in `V46MillerOracleRelativeChecks` -/

@[expose] public section
noncomputable section
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation

example (S : Set ℕ) (f : ℕ → Part ℕ) :
    HasApproximation S f ↔ Nat.RecursiveIn (oracleSet S) f :=
  OracleRelative.hasApproximation_iff_recursiveIn S f
example (p : Bits) (k : ℕ) :
    oraclePrefix {i | p i = 1} k = (bitPrefix p k).map Fin.val :=
  OracleRelative.oraclePrefix_eq p k
example (e : ℕ) (p : Bits) :
    Nat.RecursiveIn (oracleSet {k | p k = 1}) (OracleProgram.numberedEval e p) :=
  OracleRelative.numberedEval_recursiveIn e p
example (p : Bits) (f : ℕ → Part ℕ) :
    Nat.RecursiveIn (oracleSet {k | p k = 1}) f ↔
      ∃ e : ℕ, ∀ n, OracleProgram.numberedEval e p n = f n :=
  OracleRelative.recursiveIn_iff_index p f
example (p : Bits) (f : ℕ → Part ℕ)
    (hf : Nat.RecursiveIn (oracleSet {k | p k = 1}) f) :
    ∃ e : ℕ, (∀ n y, y ∈ OracleProgram.numberedEval e p n ↔ y ∈ f n) ∧
      (∀ n, (OracleProgram.numberedEval e p n).Dom ↔ (f n).Dom) :=
  OracleRelative.exists_index_graph_domain p f hf
