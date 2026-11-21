/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalTuplesStructure

/-! Explicit regularity, extensive coproducts and monomorphism inverse equations. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.NumericalTuples

example : Regular Object := inferInstance
example : FinitaryExtensive Object := inferInstance
example : HasFiniteLimits Object := inferInstance
example : HasFiniteCoproducts Object := inferInstance

example {C D : Object} (m : C ⟶ D) [Mono m] : PartialMono (splitComparison.map m) :=
  mappedMono_partialMono m

example {C D : Object} (m : C ⟶ D) [Mono m] :
    splitComparison.map m ≫ monoInverse m = 𝟙 (splitComparison.obj C) := mappedMono_inverse m

example {C D : Object} (m : C ⟶ D) [Mono m] :
    monoInverse m ≫ splitComparison.map m = rst (monoInverse m) := inverse_mappedMono m
