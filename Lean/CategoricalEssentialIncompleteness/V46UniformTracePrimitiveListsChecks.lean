/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTracePrimitiveLists


/-! # Statement checks in `V46UniformTracePrimitiveListsChecks` -/

@[expose] public section
open Nat Nat.ArithPart₁ CategoricalRiceShapiro.ArithmeticCode
open CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveCoding
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.NatVectors

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveListsChecks
example (l : List ℕ) (i : ℕ) : nativeDrop (pack l) i = pack (l.drop i) := nativeDrop_pack l i

example : Computes (codeListLength (Code.proj (0 : Fin 1)))
    (fun v => (Nat.natToList (v.get 0)).length) := computes_nativeLength (computes_proj 0)

example : PrimitiveTotal (codeListSnoc (Code.proj (0 : Fin 2)) (Code.proj (1 : Fin 2))) :=
  PrimitiveTotal.listSnoc (PrimitiveTotal.proj 0) (PrimitiveTotal.proj 1)
end CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveListsChecks
