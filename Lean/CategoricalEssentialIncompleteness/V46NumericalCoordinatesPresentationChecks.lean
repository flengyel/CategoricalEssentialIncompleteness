/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalCoordinatesPresentation


/-! # Literal predicate presentations of numerical tuples -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates

example (C : PredicateCategory 𝗧𝗔) :
    NumericalSyntax.predicateEquivalence.functor.obj C ≅ NumericalCoordinates.predicateObject C :=
  NumericalCoordinates.predicatePresentationIso C

example (C : PredicateCategory 𝗧𝗔) : (NumericalCoordinates.predicateObject C).dimension = 1 := rfl

example (C : PredicateCategory 𝗧𝗔) (n : ℕ) :
    n ∈ (NumericalCoordinates.predicateObject C).support ↔ C.val.Evalb ![n] := Iff.rfl

example (C : PredicateCategory 𝗧𝗔) :
    Partrec (NumericalCoordinates.predicatePresentationIso C).hom.restrictedProgram :=
  NumericalTuples.Map.restrictedProgram_partrec _

example (C : PredicateCategory 𝗧𝗔) :
    Partrec (NumericalCoordinates.predicatePresentationIso C).inv.restrictedProgram :=
  NumericalTuples.Map.restrictedProgram_partrec _
