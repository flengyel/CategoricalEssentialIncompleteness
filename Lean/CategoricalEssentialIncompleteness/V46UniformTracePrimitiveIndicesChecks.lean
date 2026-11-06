import CategoricalEssentialIncompleteness.V46UniformTracePrimitiveIndices

/-! # Checks for the uniform trace construction -/

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveIndicesChecks

open CategoricalEssentialIncompleteness.V46.UniformTrace

example : Nat.Primrec (constantIndex:ℕ→ℕ) := constantIndex_natPrimrec
example (v:ℕ) : Nat.Primrec (templateIndex v:ℕ→ℕ) := templateIndex_natPrimrec v

end CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveIndicesChecks
