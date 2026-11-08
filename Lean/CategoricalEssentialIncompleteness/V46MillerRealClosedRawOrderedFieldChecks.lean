import CategoricalEssentialIncompleteness.V46MillerRealClosedRawOrderedField
noncomputable section

namespace CategoricalEssentialIncompleteness.V46.Miller.RealClosedRaw
open OrderedFieldSyntax RealClosedAxioms
universe u
variable {K : Type u} (M : Interpretation K)
variable (hM : ∀ φ∈finiteMatrices,∀ ρ : ℕ → K,φ.Holds M.functions M.relations ρ)

example : Field K := fieldStructure M hM
example : LinearOrder K := linearOrderStructure M hM
example : letI : Field K := fieldStructure M hM
    letI : LinearOrder K := linearOrderStructure M hM
    IsStrictOrderedRing K := strictOrderedRing M hM
example : letI : LinearOrder K := linearOrderStructure M hM
    ∀ x y : K,x<y ↔ M.relations ⟨2,by decide⟩ ltSymbol ![x,y] := lt_comparison M hM

end CategoricalEssentialIncompleteness.V46.Miller.RealClosedRaw
