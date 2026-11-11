/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalCoordinatesPresentation

/-! # Effective coefficient coordinates at the actual tuple dimension -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalCoordinates

def codedPredicate (C : NumericalTuples.Object) : Carrier :=
  .mkSigma (codeOfREPred (fun n => n ∈ NumericalTuples.codedSupport C))
    (by simp [codeOfREPred, codeOfPartrec'])

theorem codedPredicate_eval (C : NumericalTuples.Object) (n : ℕ) :
    (codedPredicate C).val.Evalb ![n] ↔ n ∈ NumericalTuples.codedSupport C :=
  codeOfREPred_spec (NumericalTuples.codedSupport_re C)

def encodePoint (C : NumericalTuples.Object) (x : NumericalTuples.Point C) :
    NumericalTuples.Point (predicateObject (codedPredicate C)) :=
  ⟨NumericalTuples.code C.dimension x.val,
    (codedPredicate_eval C _).mpr ⟨x.val, x.property, rfl⟩⟩

def decodePoint (C : NumericalTuples.Object)
    (z : NumericalTuples.Point (predicateObject (codedPredicate C))) : NumericalTuples.Point C :=
  (NumericalTuples.pointEquiv C).symm ⟨z.val, (codedPredicate_eval C z.val).mp z.property⟩

def encode (C : NumericalTuples.Object) : C ⟶ predicateObject (codedPredicate C) where
  toFun := encodePoint C
  represented := ⟨fun x => Part.some (NumericalTuples.code C.dimension x),
    Computable.encode.partrec, fun _ => rfl⟩

def decode (C : NumericalTuples.Object) : predicateObject (codedPredicate C) ⟶ C where
  toFun := decodePoint C
  represented := ⟨NumericalTuples.decodeTuple C.dimension,
    NumericalTuples.decodeTuple_partrec C.dimension, fun z =>
      Part.eq_some_iff.mpr ((NumericalTuples.mem_decodeTuple C.dimension _ _).mpr
        (NumericalTuples.pointEquiv_symm_code C ⟨z.val, (codedPredicate_eval C z.val).mp z.property⟩))⟩

/-- Decoding is guarded at the actual dimension, including the proper
singleton image of dimension zero. -/
def codedObjectIso (C : NumericalTuples.Object) : predicateObject (codedPredicate C) ≅ C where
  hom := decode C
  inv := encode C
  hom_inv_id := by
    apply NumericalTuples.Map.ext
    funext z
    apply Subtype.ext
    exact NumericalTuples.pointEquiv_symm_code C ⟨z.val, (codedPredicate_eval C z.val).mp z.property⟩
  inv_hom_id := by
    apply NumericalTuples.Map.ext
    funext x
    exact (NumericalTuples.pointEquiv C).symm_apply_apply x

@[simp] theorem codedObjectIso_inv_value (C : NumericalTuples.Object) (x : NumericalTuples.Point C) :
    ((codedObjectIso C).inv.toFun x).val = NumericalTuples.code C.dimension x.val := rfl

@[simp] theorem codedObjectIso_hom_value (C : NumericalTuples.Object)
    (z : NumericalTuples.Point (predicateObject (codedPredicate C))) :
    NumericalTuples.code C.dimension ((codedObjectIso C).hom.toFun z).val = z.val :=
  NumericalTuples.pointEquiv_symm_code C ⟨z.val, (codedPredicate_eval C z.val).mp z.property⟩

def coefficientIso (C : NumericalTuples.Object) :
    NumericalSyntax.predicateEquivalence.functor.obj (codedPredicate C) ≅ C :=
  predicatePresentationIso (codedPredicate C) ≪≫ codedObjectIso C

end CategoricalEssentialIncompleteness.V46.NumericalCoordinates
