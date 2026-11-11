/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerUniformFinite


/-! # Statement checks in `V46MillerUniformFiniteChecks` -/

@[expose] public section
namespace CategoricalEssentialIncompleteness.V46.Miller.Uniform.Checks
example {P : Family} {α : Type} [Primcodable α] {R : α → Prop} (hR : Enumerable P R) :
    Enumerable P (fun L : List α => ∀ x ∈ L,R x) := hR.listAll
example {P : Family} {α β : Type} [Primcodable α] [Primcodable β]
    {R : α → Prop} (hR : Enumerable P R) (L : β → List α) (hL : Computable L) :
    Enumerable P (fun b => ∀ x ∈ L b,R x) := hR.finiteRecord L hL
end CategoricalEssentialIncompleteness.V46.Miller.Uniform.Checks
