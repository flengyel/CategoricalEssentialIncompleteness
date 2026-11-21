/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerTotalRealization


/-! # Finite limits, coproducts and images in the total category of the restriction splitting -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total
variable {P : Uniform.Family}
example (z : Point) : HasFiniteLimits (WideSubcategory (isTotal (C := SplitObject (Uniform.PointObject z)))) := inferInstance
example (z : Point) : HasFiniteCoproducts (CanonicalTotal z) := inferInstance
example (z : Point) : Regular (CanonicalTotal z) := inferInstance
example (z : Point) : FinitaryExtensive (CanonicalTotal z) := inferInstance
end CategoricalEssentialIncompleteness.V46.Miller.Total
