import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralSubstitutionValues

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralSubstitutionValuesChecks
open NumericalNamed
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "S₀" => literalSourceSyntax V σ π d
local notation "S₁" => literalCategoricalSyntax V σ π d
local notation "V₀" => NumericalCoordinates.codedPredicate V
local notation "σ₀" => (fun n => NumericalCoordinates.codedPredicate (σ n))
local notation "π₀" => (fun n => NumericalCoordinates.codedPredicate (π n))

example : (literalCategoricalSyntax V σ π d).termSubstitution ≫
      (literalTermPresentationIso V σ π d).hom =
    (literalTermInputPresentationIso V σ π d).hom ≫
      NumericalCoordinates.predicateMap (literalSourceSyntax V σ π d).termSubstitution :=
  literal_termSubstitution_code_square V σ π d
example : (literalCategoricalSyntax V σ π d).formulaSubstitutionOption ≫
      (literalOptionPresentationIso V σ π d).hom =
    (literalFormulaInputPresentationIso V σ π d).hom ≫
      NumericalCoordinates.predicateMap (literalSourceSyntax V σ π d).formulaSubstitutionOption :=
  literal_formulaSubstitutionOption_code_square V σ π d

example
    (q : NumericalTuples.Point ((S₁).algebra.a.1 ⨯ (S₁).substitutionParameters)) :
    let q₀ := (literalTermInputPresentationIso V σ π d).hom.toFun q
    ((literalTermPresentationIso V σ π d).hom.toFun ((S₁).termSubstitution.toFun q)).val =
      ConcreteNamedSubstitution.substitutionResult (M := ℕ) V₀ σ₀ π₀ d
        (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (S₀).substitutionParameters V₀))
          (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance ((S₀).algebra.a.1 ⨯ (S₀).substitutionParameters) (S₀).substitutionParameters)) q₀)).val
        (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (S₀).substitutionParameters (S₀).algebra.a.1))
          (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance ((S₀).algebra.a.1 ⨯ (S₀).substitutionParameters) (S₀).substitutionParameters)) q₀)).val
        (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance ((S₀).algebra.a.1 ⨯ (S₀).substitutionParameters) (S₀).algebra.a.1)) q₀).val :=
  literal_termSubstitution_value V σ π d q

example
    (q : NumericalTuples.Point ((S₁).algebra.a.2 ⨯ (S₁).substitutionParameters)) :
    let q₀ := (literalFormulaInputPresentationIso V σ π d).hom.toFun q
    ConcreteNamedComparison.optionCode 𝗧𝗔 ℕ (S₀).algebra.a.2
      ((literalOptionPresentationIso V σ π d).hom.toFun ((S₁).formulaSubstitutionOption.toFun q)) =
      ConcreteNamedSubstitution.substitutionResult (M := ℕ) V₀ σ₀ π₀ d
        (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (S₀).substitutionParameters V₀))
          (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).substitutionParameters)) q₀)).val
        (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (S₀).substitutionParameters (S₀).algebra.a.1))
          (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).substitutionParameters)) q₀)).val
        (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).algebra.a.2)) q₀).val :=
  literal_formulaSubstitutionOption_value V σ π d q

end CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralSubstitutionValuesChecks
