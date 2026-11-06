import CategoricalEssentialIncompleteness.V46SyntacticSyntaxOccurrenceComparisonTotal

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntaxOccurrenceComparisonTotalChecks
open ConcreteSyntaxOperationsTransport SyntaxOperationsTransport
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : TotalSplit T) (σ π : ℕ → TotalSplit T) (d : ℕ)
local notation "E" => predicateEquivalence T
local notation "S₀" => sourceSyntax T V σ π d
local notation "S₁" => targetSyntax T V σ π d
example : (E).functor.map (S₀).termOccurrences ≫
      (syntaxListIso (E) V σ π d (S₀) (S₁) (targetListsEquality T V σ π d)).hom =
    (syntaxTermIso («S₁» := (S₁)) (E) V σ π d (S₀) (algebraIso T V σ π d)).hom ≫
      (S₁).termOccurrences :=
  (termOccurrenceComparison_iff (E) V σ π d (S₀) (S₁)
    (targetListsEquality T V σ π d) (algebraIso T V σ π d)).mp
      (termOccurrences_comparison T V σ π d)
example : (E).functor.map (S₀).formulaOccurrences ≫
      (syntaxListIso (E) V σ π d (S₀) (S₁) (targetListsEquality T V σ π d)).hom =
    (syntaxFormulaIso («S₁» := (S₁)) (E) V σ π d (S₀) (algebraIso T V σ π d)).hom ≫
      (S₁).formulaOccurrences :=
  (formulaOccurrenceComparison_iff (E) V σ π d (S₀) (S₁)
    (targetListsEquality T V σ π d) (algebraIso T V σ π d)).mp
      (formulaOccurrences_comparison T V σ π d)
end CategoricalEssentialIncompleteness.V46.SyntacticSyntaxOccurrenceComparisonTotalChecks
