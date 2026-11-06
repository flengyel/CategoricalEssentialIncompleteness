import CategoricalEssentialIncompleteness.V46UniformTracePrimitiveBuilders

/-! # Checks for the uniform trace construction -/

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveBuildersChecks

open CategoricalEssentialIncompleteness.V46.UniformTrace

example : Nat.Primrec (Nat.unpaired (compose:ℕ→ℕ→ℕ)) := compose_natPrimrec
example : Nat.Primrec (Nat.unpaired (specialize:ℕ→ℕ→ℕ)) := specialize_natPrimrec

end CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveBuildersChecks
