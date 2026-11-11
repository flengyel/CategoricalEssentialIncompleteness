/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerListsCarrier


/-! # Statement checks in `V46MillerListsCarrierChecks` -/

@[expose] public section
noncomputable section
open CategoryTheory FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.Miller
variable {P : Uniform.Family}
example (V : Total.Carrier P) : Uniform.Enumerable P (fun n => n ∈ (Lists.carrier V).support) :=
  (Lists.carrier V).enumerable
example (V : Total.Carrier P) : 0 ∈ (Lists.carrier V).support := Lists.nil_mem V
example (V : Total.Carrier P) (v rest : ℕ) :
    adjoin v rest ∈ (Lists.carrier V).support ↔ v ∈ V.support ∧ rest ∈ (Lists.carrier V).support :=
  Lists.adjoin_mem V v rest
example (V : Total.Carrier P) (v rest y : ℕ) :
    y ∈ Total.val (Lists.adjoinMap V).hom (Nat.pair v rest) ↔
      v ∈ V.support ∧ rest ∈ (Lists.carrier V).support ∧ y=adjoin v rest := Lists.adjoin_graph V v rest y
