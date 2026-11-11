/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralOperations
public import CategoricalEssentialIncompleteness.V46NumericalNamedValueCertificate
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPlainOccurrences

/-! # Literal numerical free-variable diagrams and primitive traversal values -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalNamed
open SyntaxOperationsTransport

variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "E" => literalEquivalence
local notation "S₀" => literalSourceSyntax V σ π d
local notation "S₁" => literalCategoricalSyntax V σ π d
local notation "V₀" => NumericalCoordinates.codedPredicate V
local notation "σ₀" => (fun n => NumericalCoordinates.codedPredicate (σ n))
local notation "π₀" => (fun n => NumericalCoordinates.codedPredicate (π n))

theorem literal_termOccurrences_code_square :
    (S₁).termOccurrences ≫ (literalListPresentationIso V σ π d).hom =
      (literalTermPresentationIso V σ π d).hom ≫
        NumericalCoordinates.predicateMap (S₀).termOccurrences :=
  conjugate_operation ((E).functor.map (S₀).termOccurrences) (S₁).termOccurrences
    (literalTermIso V σ π d) (literalListIso V σ π d)
    (NumericalCoordinates.predicatePresentationIso (S₀).algebra.a.1)
    (NumericalCoordinates.predicatePresentationIso (S₀).lists.algebra.carrier)
    ((termOccurrenceComparison_iff (E) V σ π d (S₀) (S₁)
      (literalListsEquality V σ π d) (literalAlgebraIso V σ π d)).mp
        (literal_termOccurrences_comparison V σ π d))

theorem literal_formulaOccurrences_code_square :
    (S₁).formulaOccurrences ≫ (literalListPresentationIso V σ π d).hom =
      (literalFormulaPresentationIso V σ π d).hom ≫
        NumericalCoordinates.predicateMap (S₀).formulaOccurrences :=
  conjugate_operation ((E).functor.map (S₀).formulaOccurrences) (S₁).formulaOccurrences
    (literalFormulaIso V σ π d) (literalListIso V σ π d)
    (NumericalCoordinates.predicatePresentationIso (S₀).algebra.a.2)
    (NumericalCoordinates.predicatePresentationIso (S₀).lists.algebra.carrier)
    ((formulaOccurrenceComparison_iff (E) V σ π d (S₀) (S₁)
      (literalListsEquality V σ π d) (literalAlgebraIso V σ π d)).mp
        (literal_formulaOccurrences_comparison V σ π d))

theorem literal_termOccurrences_value (x : NumericalTuples.Point (S₁).algebra.a.1) :
    ((literalListPresentationIso V σ π d).hom.toFun ((S₁).termOccurrences.toFun x)).val =
      ConcreteNamedSubstitution.freeVariables (M := ℕ) V₀ σ₀ π₀ d
        ((literalTermPresentationIso V σ π d).hom.toFun x).val :=
  predicate_operation_value (S₀).termOccurrences (S₁).termOccurrences
    (literalTermPresentationIso V σ π d) (literalListPresentationIso V σ π d)
    (literal_termOccurrences_code_square V σ π d) Subtype.val
    (fun w => ConcreteNamedSubstitution.freeVariables (M := ℕ) V₀ σ₀ π₀ d w.val)
    (ConcreteNamedComparison.plain_termOccurrences_value 𝗧𝗔 V₀ σ₀ π₀ d ℕ) x

theorem literal_formulaOccurrences_value (x : NumericalTuples.Point (S₁).algebra.a.2) :
    ((literalListPresentationIso V σ π d).hom.toFun ((S₁).formulaOccurrences.toFun x)).val =
      ConcreteNamedSubstitution.freeVariables (M := ℕ) V₀ σ₀ π₀ d
        ((literalFormulaPresentationIso V σ π d).hom.toFun x).val :=
  predicate_operation_value (S₀).formulaOccurrences (S₁).formulaOccurrences
    (literalFormulaPresentationIso V σ π d) (literalListPresentationIso V σ π d)
    (literal_formulaOccurrences_code_square V σ π d) Subtype.val
    (fun w => ConcreteNamedSubstitution.freeVariables (M := ℕ) V₀ σ₀ π₀ d w.val)
    (ConcreteNamedComparison.plain_formulaOccurrences_value 𝗧𝗔 V₀ σ₀ π₀ d ℕ) x

end CategoricalEssentialIncompleteness.V46.NumericalNamed
