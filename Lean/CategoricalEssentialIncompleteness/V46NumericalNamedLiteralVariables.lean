/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralEquivalence
import CategoricalEssentialIncompleteness.V46NamedPostfixEncoding

/-! # Literal variable names and the effective coefficient-code diagrams -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalNamed

theorem codedPredicate_predicateObject_eval (C : PredicateCategory 𝗧𝗔) (n : ℕ) :
    (NumericalCoordinates.codedPredicate (NumericalCoordinates.predicateObject C)).val.Evalb ![n] ↔
      C.val.Evalb ![n] :=
  (NumericalCoordinates.codedPredicate_eval (NumericalCoordinates.predicateObject C) n).trans
    (NumericalTuples.code_mem_codedSupport (NumericalCoordinates.predicateObject C) n)

def variableObject : NumericalTuples.Object := ⟨1, Set.univ, REPred.const True⟩
def variablePoint (n : ℕ) : NumericalTuples.Point variableObject := ⟨n, Set.mem_univ _⟩

theorem codedVariable_member (n : ℕ) :
    (NumericalCoordinates.codedPredicate variableObject).val.Evalb ![n] :=
  (NumericalCoordinates.codedPredicate_eval variableObject n).mpr ⟨n, Set.mem_univ _, rfl⟩

theorem codedVariable_literal (n : ℕ) :
    (NumericalCoordinates.codedPredicate variableObject).val.Evalb ![n] ↔
      NamedPostfixEncoding.variableCarrier.val.Evalb ![n] := by
  constructor
  · intro _
    simp [NamedPostfixEncoding.variableCarrier]
  · intro _
    exact codedVariable_member n

/-- The numerical inverse coefficient chart encodes the actual tuple;
the two presentation maps cancel as numerical morphisms. -/
theorem coefficient_inverse_code {C : NumericalTuples.Object} (x : NumericalTuples.Point C) :
    ((NumericalCoordinates.predicatePresentationIso (NumericalCoordinates.codedPredicate C)).hom.toFun
      ((NumericalCoordinates.coefficientIso C).inv.toFun x)).val =
        NumericalTuples.code C.dimension x.val := by
  have h : (NumericalCoordinates.coefficientIso C).inv ≫
      (NumericalCoordinates.predicatePresentationIso (NumericalCoordinates.codedPredicate C)).hom =
        (NumericalCoordinates.codedObjectIso C).inv := by
    simp only [NumericalCoordinates.coefficientIso, Iso.trans_inv, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  exact (congrArg (fun f => (f.toFun x).val) h).trans
    (NumericalCoordinates.codedObjectIso_inv_value C x)

theorem variable_name_code (n : ℕ) :
    ((NumericalCoordinates.predicatePresentationIso (NumericalCoordinates.codedPredicate variableObject)).hom.toFun
      ((literalEquivalence.counitIso.app variableObject).inv.toFun (variablePoint n))).val = n :=
  coefficient_inverse_code (variablePoint n)

end CategoricalEssentialIncompleteness.V46.NumericalNamed
