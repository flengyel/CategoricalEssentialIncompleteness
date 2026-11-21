/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerTotalInverses


/-! # Uniform partial inverses on semidecidable images -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total
variable {P : Uniform.Family}
example : WeakChoice (Carrier P) := inferInstance
example {X Y : Carrier P} (f : X ⟶ Y) (hf : PartialMono f) : Injective f := injective_of_partialMono f hf
example {X Y : Carrier P} (f : X ⟶ Y) (hf : Injective f) :
    ∃ s : Y ⟶ X,∀ y x,x ∈ val s y ↔ y ∈ val f x := exists_inverse f hf
example {X Y : Carrier P} (f : X ⟶ Y) : Surjective f ↔ Ranges.range f = ⊤ := surjective_iff_range_top f
end CategoricalEssentialIncompleteness.V46.Miller.Total
