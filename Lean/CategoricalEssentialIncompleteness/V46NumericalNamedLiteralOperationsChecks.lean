/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralOperations


/-! # Statement checks in `V46NumericalNamedLiteralOperationsChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralOperationsChecks
open NumericalNamed SyntaxOperationsTransport
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "E" => literalEquivalence
local notation "S₀" => literalSourceSyntax V σ π d
local notation "S₁" => literalCategoricalSyntax V σ π d

example : (E).functor.map (S₀).termOccurrences ≫ (literalListIso V σ π d).hom =
    (literalTermIso V σ π d).hom ≫ (S₁).termOccurrences :=
  (termOccurrenceComparison_iff (E) V σ π d (S₀) (S₁)
    (literalListsEquality V σ π d) (literalAlgebraIso V σ π d)).mp
      (literal_termOccurrences_comparison V σ π d)
example : (E).functor.map (S₀).formulaOccurrences ≫ (literalListIso V σ π d).hom =
    (literalFormulaIso V σ π d).hom ≫ (S₁).formulaOccurrences :=
  (formulaOccurrenceComparison_iff (E) V σ π d (S₀) (S₁)
    (literalListsEquality V σ π d) (literalAlgebraIso V σ π d)).mp
      (literal_formulaOccurrences_comparison V σ π d)
example : (E).functor.map (S₀).termSubstitution ≫ (literalTermIso V σ π d).hom =
    (SyntaxOptionTransport.productIso (E) (literalTermIso V σ π d)
      (substitutionParameterIso (E) V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d))).hom ≫
        (S₁).termSubstitution :=
  (termSubstitutionComparison_iff (E) V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d)).mp
    (literal_termSubstitution_comparison V σ π d)
example : (E).functor.map (S₀).formulaSubstitutionOption ≫
      (SyntaxOptionTransport.optionIso (E) (literalFormulaIso V σ π d)).hom =
    (SyntaxOptionTransport.productIso (E) (literalFormulaIso V σ π d)
      (substitutionParameterIso (E) V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d))).hom ≫
        (S₁).formulaSubstitutionOption :=
  (formulaSubstitutionOptionComparison_iff (E) V σ π d (S₀) (S₁)
    (literalAlgebraIso V σ π d)).mp (literal_formulaSubstitutionOption_comparison V σ π d)
example : (literalAdmissibleIso V σ π d).hom ≫ (S₁).admissibleInclusion =
    (E).functor.map (S₀).admissibleInclusion ≫
      (SyntaxOptionTransport.productIso (E) (literalFormulaIso V σ π d)
        (substitutionParameterIso (E) V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d))).hom :=
  literalAdmissibleIso_inclusion V σ π d
example : (literalAdmissibleIso V σ π d).hom ≫ (S₁).formulaSubstitution =
    (E).functor.map (S₀).formulaSubstitution ≫ (literalFormulaIso V σ π d).hom :=
  literalAdmissibleIso_result V σ π d

end CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralOperationsChecks
