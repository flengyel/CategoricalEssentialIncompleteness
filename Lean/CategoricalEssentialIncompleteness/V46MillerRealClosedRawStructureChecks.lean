import CategoricalEssentialIncompleteness.V46MillerRealClosedRawStructure

namespace CategoricalEssentialIncompleteness.V46.Miller.RealClosedRaw
open OrderedFieldSyntax RealClosedAxioms
universe u
example {K : Type u} (M : Interpretation K)
    (hM : ∀ φ∈finiteMatrices,∀ ρ : ℕ → K,φ.Holds M.functions M.relations ρ) :
    MatrixConsequences M := matrix_consequences M hM
end CategoricalEssentialIncompleteness.V46.Miller.RealClosedRaw
