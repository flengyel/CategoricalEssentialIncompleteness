/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerRealClosedRawStructure


/-! # Statement checks in `V46MillerRealClosedRawStructureChecks` -/

@[expose] public section
namespace CategoricalEssentialIncompleteness.V46.Miller.RealClosedRaw
open OrderedFieldSyntax RealClosedAxioms
universe u
example {K : Type u} (M : Interpretation K)
    (hM : ∀ φ∈finiteMatrices,∀ ρ : ℕ → K,φ.Holds M.functions M.relations ρ) :
    MatrixConsequences M := matrix_consequences M hM
end CategoricalEssentialIncompleteness.V46.Miller.RealClosedRaw
