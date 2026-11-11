/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxOccurrenceComparisonTotal
public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportMappedLists

/-! # Concrete substitution transport in the total restriction splitting

The comparison uses the constructor-preserving algebra isomorphism already
constructed from initiality, and the actual mapped stable-list record.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ConcreteSyntaxOperationsTransport
open SyntacticSyntax SyntacticLists.Transport SyntaxOperationsTransport
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : TotalSplit T) (σ π : ℕ → TotalSplit T) (d : ℕ)
local notation "E" => predicateEquivalence T
local notation "S₀" => sourceSyntax T V σ π d
local notation "S₁" => targetSyntax T V σ π d

/-- The actual term-substitution square, with the named parameter coordinate
transported by the same constructor-preserving syntax comparison. -/
theorem termSubstitution_comparison :
    termSubstitutionComparison (E) V σ π d (S₀) (S₁) (algebraIso T V σ π d) :=
  mapped_termSubstitution_comparison (E) V σ π d (S₀) (S₁)
    (targetListsEquality T V σ π d) (algebraIso T V σ π d)

/-- The complete option-valued formula-substitution square. -/
theorem formulaSubstitutionOption_comparison :
    formulaSubstitutionOptionComparison (E) V σ π d (S₀) (S₁)
      (algebraIso T V σ π d) :=
  mapped_formulaSubstitutionOption_comparison (E) V σ π d (S₀) (S₁)
    (targetListsEquality T V σ π d) (algebraIso T V σ π d)

/-- Transport of the actual success pullback defining admissibility. -/
def admissibleIso : (E).functor.obj (S₀).admissibleSubstitution ≅
    (S₁).admissibleSubstitution :=
  mappedAdmissibleSubstitutionIso (E) V σ π d (S₀) (S₁)
    (targetListsEquality T V σ π d) (algebraIso T V σ π d)

@[reassoc] theorem admissibleIso_inclusion :
    (mappedAdmissibleSubstitutionIso (E) V σ π d (S₀) (S₁)
      (targetListsEquality T V σ π d) (algebraIso T V σ π d)).hom ≫
        (S₁).admissibleInclusion =
      (E).functor.map (S₀).admissibleInclusion ≫
        (SyntaxOptionTransport.productIso (E)
          (X := (S₀).algebra.a.2) (Y := (S₀).substitutionParameters)
          (syntaxFormulaIso («S₁» := (S₁)) (E) V σ π d (S₀)
            (algebraIso T V σ π d))
          (substitutionParameterIso (E) V σ π d (S₀) (S₁)
            (algebraIso T V σ π d))).hom :=
  mappedAdmissibleSubstitutionIso_inclusion (E) V σ π d (S₀) (S₁)
    (targetListsEquality T V σ π d) (algebraIso T V σ π d)

@[reassoc] theorem admissibleIso_result :
    (mappedAdmissibleSubstitutionIso (E) V σ π d (S₀) (S₁)
      (targetListsEquality T V σ π d) (algebraIso T V σ π d)).hom ≫
        (S₁).formulaSubstitution =
      (E).functor.map (S₀).formulaSubstitution ≫
        (syntaxFormulaIso («S₁» := (S₁)) (E) V σ π d (S₀)
          (algebraIso T V σ π d)).hom :=
  mappedAdmissibleSubstitutionIso_result (E) V σ π d (S₀) (S₁)
    (targetListsEquality T V σ π d) (algebraIso T V σ π d)

end CategoricalEssentialIncompleteness.V46.ConcreteSyntaxOperationsTransport
