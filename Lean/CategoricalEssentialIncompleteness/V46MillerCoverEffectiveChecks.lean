import CategoricalEssentialIncompleteness.V46MillerCoverEffective
noncomputable section
namespace CategoricalEssentialIncompleteness.V46.Miller.Unanimity.Checks
example : REPred (fun t : (Word × Input) × ℕ => Certified t.1.1 t.1.2 t.2) := certified_re
example : ∃ F : List ℕ × ℕ → Part ℕ, Partrec F ∧
    LocalConnectedness.OracleComputation.MonotoneValues F ∧
    ∀ l n m, m ∈ F (l,n) ↔ Certified (normalizeWord l) (Nat.unpair n) m := table_program
end CategoricalEssentialIncompleteness.V46.Miller.Unanimity.Checks
