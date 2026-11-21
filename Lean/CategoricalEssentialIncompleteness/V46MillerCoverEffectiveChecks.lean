/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCoverEffective


/-! # An ordinary semidecision program for successful finite covers -/

@[expose] public section
noncomputable section
namespace CategoricalEssentialIncompleteness.V46.Miller.Unanimity.Checks
example : REPred (fun t : (Word × Input) × ℕ => Certified t.1.1 t.1.2 t.2) := certified_re
example : ∃ F : List ℕ × ℕ → Part ℕ, Partrec F ∧
    LocalConnectedness.OracleComputation.MonotoneValues F ∧
    ∀ l n m, m ∈ F (l,n) ↔ Certified (normalizeWord l) (Nat.unpair n) m := table_program
end CategoricalEssentialIncompleteness.V46.Miller.Unanimity.Checks
