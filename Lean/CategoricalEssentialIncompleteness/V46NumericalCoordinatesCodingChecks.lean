/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalCoordinatesCoding


/-! # Effective coefficient coordinates at the tuple dimension -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates

example (C : NumericalTuples.Object) (n : ℕ) :
    (NumericalCoordinates.codedPredicate C).val.Evalb ![n] ↔ n ∈ NumericalTuples.codedSupport C :=
  NumericalCoordinates.codedPredicate_eval C n

example (C : NumericalTuples.Object) :
    NumericalSyntax.predicateEquivalence.functor.obj (NumericalCoordinates.codedPredicate C) ≅ C :=
  NumericalCoordinates.coefficientIso C

example (C : NumericalTuples.Object) (x : NumericalTuples.Point C) :
    ((NumericalCoordinates.codedObjectIso C).inv.toFun x).val =
      NumericalTuples.code C.dimension x.val :=
  NumericalCoordinates.codedObjectIso_inv_value C x

example (C : NumericalTuples.Object) :
    Partrec (NumericalCoordinates.codedObjectIso C).hom.program :=
  NumericalTuples.Map.program_partrec _

example (C : NumericalTuples.Object) :
    Partrec (NumericalCoordinates.codedObjectIso C).inv.program :=
  NumericalTuples.Map.program_partrec _

example (n : ℕ) :
    (NumericalCoordinates.codedPredicate NumericalTuples.terminalObject).val.Evalb ![n] ↔ n = 0 := by
  rw [NumericalCoordinates.codedPredicate_eval]
  change (∃ x : NumericalTuples.Tuple 0,
    x ∈ (Set.univ : Set (NumericalTuples.Tuple 0)) ∧ NumericalTuples.code 0 x = n) ↔ n = 0
  constructor
  · rintro ⟨x, _, h⟩
    simpa using h.symm
  · intro h
    exact ⟨(), Set.mem_univ _, h.symm⟩
