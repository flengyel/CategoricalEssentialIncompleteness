import CategoricalEssentialIncompleteness.V46SyntacticSyntaxSubstitutionComparisonTotal

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntaxSubstitutionComparisonTotalChecks
open ConcreteSyntaxOperationsTransport SyntaxOperationsTransport
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : TotalSplit T) (σ π : ℕ → TotalSplit T) (d : ℕ)
local notation "E" => predicateEquivalence T
local notation "S₀" => sourceSyntax T V σ π d
local notation "S₁" => targetSyntax T V σ π d

example : (E).functor.map (S₀).termSubstitution ≫
      (syntaxTermIso («S₁» := (S₁)) (E) V σ π d (S₀)
        (algebraIso T V σ π d)).hom =
    (SyntaxOptionTransport.productIso (E)
      (X := (S₀).algebra.a.1) (Y := (S₀).substitutionParameters)
      (syntaxTermIso («S₁» := (S₁)) (E) V σ π d (S₀) (algebraIso T V σ π d))
      (substitutionParameterIso (E) V σ π d (S₀) (S₁) (algebraIso T V σ π d))).hom ≫
        (S₁).termSubstitution :=
  (termSubstitutionComparison_iff (E) V σ π d (S₀) (S₁)
    (algebraIso T V σ π d)).mp (termSubstitution_comparison T V σ π d)

example : (E).functor.map (S₀).formulaSubstitutionOption ≫
      (SyntaxOptionTransport.optionIso (E) (X := (S₀).algebra.a.2)
        (syntaxFormulaIso («S₁» := (S₁)) (E) V σ π d (S₀)
          (algebraIso T V σ π d))).hom =
    (SyntaxOptionTransport.productIso (E)
      (X := (S₀).algebra.a.2) (Y := (S₀).substitutionParameters)
      (syntaxFormulaIso («S₁» := (S₁)) (E) V σ π d (S₀) (algebraIso T V σ π d))
      (substitutionParameterIso (E) V σ π d (S₀) (S₁) (algebraIso T V σ π d))).hom ≫
        (S₁).formulaSubstitutionOption :=
  (formulaSubstitutionOptionComparison_iff (E) V σ π d (S₀) (S₁)
    (algebraIso T V σ π d)).mp (formulaSubstitutionOption_comparison T V σ π d)

example : (mappedAdmissibleSubstitutionIso (E) V σ π d (S₀) (S₁)
      (targetListsEquality T V σ π d) (algebraIso T V σ π d)).hom ≫
        (S₁).admissibleInclusion =
    (E).functor.map (S₀).admissibleInclusion ≫
      (SyntaxOptionTransport.productIso (E)
        (X := (S₀).algebra.a.2) (Y := (S₀).substitutionParameters)
        (syntaxFormulaIso («S₁» := (S₁)) (E) V σ π d (S₀) (algebraIso T V σ π d))
        (substitutionParameterIso (E) V σ π d (S₀) (S₁) (algebraIso T V σ π d))).hom :=
  admissibleIso_inclusion T V σ π d

example : (mappedAdmissibleSubstitutionIso (E) V σ π d (S₀) (S₁)
      (targetListsEquality T V σ π d) (algebraIso T V σ π d)).hom ≫
        (S₁).formulaSubstitution =
    (E).functor.map (S₀).formulaSubstitution ≫
      (syntaxFormulaIso («S₁» := (S₁)) (E) V σ π d (S₀) (algebraIso T V σ π d)).hom :=
  admissibleIso_result T V σ π d

end CategoricalEssentialIncompleteness.V46.SyntacticSyntaxSubstitutionComparisonTotalChecks
