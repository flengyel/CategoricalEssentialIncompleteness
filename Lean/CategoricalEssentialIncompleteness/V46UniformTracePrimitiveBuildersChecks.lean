/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTracePrimitiveBuilders

/-! # Checks for the uniform trace construction -/

@[expose] public section

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveBuildersChecks

open CategoricalEssentialIncompleteness.V46.UniformTrace

example : Nat.Primrec (Nat.unpaired (compose:ℕ→ℕ→ℕ)) := compose_natPrimrec
example : Nat.Primrec (Nat.unpaired (specialize:ℕ→ℕ→ℕ)) := specialize_natPrimrec

end CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveBuildersChecks
