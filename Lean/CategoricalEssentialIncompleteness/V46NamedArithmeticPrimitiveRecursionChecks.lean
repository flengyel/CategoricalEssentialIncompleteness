/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticPrimitiveRecursion


/-! # Statement checks in `V46NamedArithmeticPrimitiveRecursionChecks` -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.NamedArithmeticPrimitiveRecursion
example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {p : PR.Blueprint 0} (c : PR.Construction M p) (out n : M) :
    p.resultDef.val.Evalb ![out,n] ↔ out = scalarResult c n := scalarResult_eval c out n
example {p : PR.Blueprint 0} (c : PR.Construction ℕ p)
    (hz : Primrec (fun _ : Unit => c.zero ![]))
    (hs : Primrec₂ (fun (_ : Unit) (v : ℕ × ℕ) => c.succ ![] v.1 v.2)) :
    Primrec (scalarResult c) := scalarResult_primrec c hz hs
