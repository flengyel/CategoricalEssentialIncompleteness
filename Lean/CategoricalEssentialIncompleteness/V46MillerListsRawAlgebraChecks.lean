/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerListsRawAlgebra


/-! # Statement checks in `V46MillerListsRawAlgebraChecks` -/

@[expose] public section
noncomputable section
open CategoryTheory FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.Miller
variable {P : Uniform.Family} (R : Total.TotalCategory P) (V : Total.Carrier P)
example : Syntax.Raw.object R (Lists.family R V) (Lists.family R V) .unit ⟶ Lists.family R V := Lists.rawNil R V
example (r head tail out : ℕ) :
    out ∈ Total.val (Lists.rawCons R V).left.hom (Nat.pair r (Nat.pair head (Nat.pair r tail))) ↔
      r ∈ R.obj.support ∧ head ∈ V.support ∧ tail ∈ (Lists.carrier V).support ∧ out=Nat.pair r (adjoin head tail) :=
  Lists.rawCons_graph R V r head tail out
