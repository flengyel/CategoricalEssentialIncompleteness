/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralSyntax

/-! # Actual folds and admissibility for literal numerical syntax -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalNamed
open SyntaxOperationsTransport
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "E" => literalEquivalence
local notation "S₀" => literalSourceSyntax V σ π d
local notation "S₁" => literalCategoricalSyntax V σ π d

theorem literal_termOccurrences_comparison :
    termOccurrenceComparison (E) V σ π d (S₀) (S₁)
      (literalListsEquality V σ π d) (literalAlgebraIso V σ π d) :=
  mapped_termOccurrence_comparison (E) V σ π d (S₀) (S₁)
    (literalListsEquality V σ π d) (literalAlgebraIso V σ π d)

theorem literal_formulaOccurrences_comparison :
    formulaOccurrenceComparison (E) V σ π d (S₀) (S₁)
      (literalListsEquality V σ π d) (literalAlgebraIso V σ π d) :=
  mapped_formulaOccurrence_comparison (E) V σ π d (S₀) (S₁)
    (literalListsEquality V σ π d) (literalAlgebraIso V σ π d)

theorem literal_termSubstitution_comparison :
    termSubstitutionComparison (E) V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d) :=
  mapped_termSubstitution_comparison (E) V σ π d (S₀) (S₁)
    (literalListsEquality V σ π d) (literalAlgebraIso V σ π d)

theorem literal_formulaSubstitutionOption_comparison :
    formulaSubstitutionOptionComparison (E) V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d) :=
  mapped_formulaSubstitutionOption_comparison (E) V σ π d (S₀) (S₁)
    (literalListsEquality V σ π d) (literalAlgebraIso V σ π d)

def literalAdmissibleIso : (E).functor.obj (S₀).admissibleSubstitution ≅ (S₁).admissibleSubstitution :=
  mappedAdmissibleSubstitutionIso (E) V σ π d (S₀) (S₁)
    (literalListsEquality V σ π d) (literalAlgebraIso V σ π d)

@[reassoc] theorem literalAdmissibleIso_inclusion :
    (literalAdmissibleIso V σ π d).hom ≫ (S₁).admissibleInclusion =
      (E).functor.map (S₀).admissibleInclusion ≫
        (SyntaxOptionTransport.productIso (E)
          (syntaxFormulaIso («S₁» := (S₁)) (E) V σ π d (S₀) (literalAlgebraIso V σ π d))
          (substitutionParameterIso (E) V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d))).hom :=
  mappedAdmissibleSubstitutionIso_inclusion (E) V σ π d (S₀) (S₁)
    (literalListsEquality V σ π d) (literalAlgebraIso V σ π d)

@[reassoc] theorem literalAdmissibleIso_result :
    (literalAdmissibleIso V σ π d).hom ≫ (S₁).formulaSubstitution =
      (E).functor.map (S₀).formulaSubstitution ≫ (literalFormulaIso V σ π d).hom :=
  mappedAdmissibleSubstitutionIso_result (E) V σ π d (S₀) (S₁)
    (literalListsEquality V σ π d) (literalAlgebraIso V σ π d)

/-- These are morphisms to the literal accepted words with actual tuple-code labels. -/
def literalTermPresentationIso : (S₁).algebra.a.1 ≅
    NumericalCoordinates.predicateObject (S₀).algebra.a.1 :=
  (literalTermIso V σ π d).symm ≪≫ NumericalCoordinates.predicatePresentationIso (S₀).algebra.a.1

def literalFormulaPresentationIso : (S₁).algebra.a.2 ≅
    NumericalCoordinates.predicateObject (S₀).algebra.a.2 :=
  (literalFormulaIso V σ π d).symm ≪≫ NumericalCoordinates.predicatePresentationIso (S₀).algebra.a.2

def literalListPresentationIso : (S₁).lists.algebra.carrier ≅
    NumericalCoordinates.predicateObject (S₀).lists.algebra.carrier :=
  (literalListIso V σ π d).symm ≪≫
    NumericalCoordinates.predicatePresentationIso (S₀).lists.algebra.carrier

end CategoricalEssentialIncompleteness.V46.NumericalNamed
