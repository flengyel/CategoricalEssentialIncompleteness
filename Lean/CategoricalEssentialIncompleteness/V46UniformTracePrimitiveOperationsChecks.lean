/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTracePrimitiveOperations


/-! # Constructing standard primitive values for the arithmetic codes -/

@[expose] public section
open Nat Nat.ArithPart₁ CategoricalRiceShapiro.ArithmeticCode
open CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveCoding

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveOperationsChecks
example : PrimitiveTotal (codePartrecTag (Code.proj (0 : Fin 1))) :=
  PrimitiveTotal.partrecTag (PrimitiveTotal.proj 0)

example : PrimitiveTotal (codePartrecPayload₂ (Code.proj (0 : Fin 1))) :=
  PrimitiveTotal.partrecPayload2 (PrimitiveTotal.proj 0)

example {n : ℕ} (c : Code n) (d : Code (n + 2))
    (hc : PrimitiveTotal c) (hd : PrimitiveTotal d) :
    ∃ f : List.Vector ℕ (n + 1) → ℕ, Computes (codePrec c d) f ∧ Primrec f :=
  PrimitiveTotal.prec hc hd
end CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveOperationsChecks
