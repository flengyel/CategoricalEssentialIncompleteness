import CategoricalEssentialIncompleteness.V46NumericalTuplesStructure

/-! Explicit regularity, extensive coproducts and actual monomorphism inverse equations. -/

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
