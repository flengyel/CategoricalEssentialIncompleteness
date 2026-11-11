/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticCodedMaps


/-! # Statement checks in `V46NumericalArithmeticCodedMapsChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.CodedMaps.Checks
variable {X Y : NumericalTuples.Object} (f : X ⟶ Y)
example : NumericalCoordinates.predicateMap (encodedMap f) ≫ (NumericalCoordinates.codedObjectIso Y).hom =
    (NumericalCoordinates.codedObjectIso X).hom ≫ f := decode_natural f
example (a b : ℕ) : (graph f).val.Evalb ![a,b] ↔
    ∃ x : NumericalTuples.Point X, NumericalTuples.code X.dimension x.val = a ∧
      NumericalTuples.code Y.dimension (f.toFun x).val = b := graph_eval f a b
example (b : ℕ) : (imagePredicate f).val.Evalb ![b] ↔
    ∃ x : NumericalTuples.Point X, NumericalTuples.code Y.dimension (f.toFun x).val = b :=
  imagePredicate_eval f b
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.CodedMaps.Checks
