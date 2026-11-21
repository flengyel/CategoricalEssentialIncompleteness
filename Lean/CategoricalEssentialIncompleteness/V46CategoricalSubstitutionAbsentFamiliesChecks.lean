/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionAbsentFamilies

/-! The invariant compares value morphisms over one unchanged parameter. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {P V U Y : D} (L : StableListAlgebra V) (E : DecidableVariables V)
variable (name : P ⟶ V) (FV : U ⟶ L.algebra.carrier) (embed : U ⟶ Y)

example {X : Over P} (m : X ⟶ constantFamily P (U ⨯ Y)) :
    m ≫ AbsentFamilies.mask L E name FV embed = m ≫ AbsentFamilies.result ↔
      ConditionalInvariant.Holds
        (prod.lift (X.hom ≫ name) (m.left ≫ prod.snd ≫ prod.fst ≫ FV) ≫ L.membership E)
        (m.left ≫ prod.snd ≫ prod.fst ≫ embed) (m.left ≫ prod.snd ≫ prod.snd) :=
  AbsentFamilies.equation_iff L E name FV embed m
