/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTracePrimitiveIndices

/-! # Checks for the uniform trace construction -/

@[expose] public section

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveIndicesChecks

open CategoricalEssentialIncompleteness.V46.UniformTrace

example : Nat.Primrec (constantIndex:ℕ→ℕ) := constantIndex_natPrimrec
example (v:ℕ) : Nat.Primrec (templateIndex v:ℕ→ℕ) := templateIndex_natPrimrec v

end CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveIndicesChecks
