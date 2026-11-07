import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralInputValues

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralInputValuesChecks
open NumericalNamed
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "S₀" => literalSourceSyntax V σ π d
local notation "S₁" => literalCategoricalSyntax V σ π d
local notation "F" => PredicateInterpretation.functor 𝗧𝗔 ℕ

example (q : NumericalTuples.Point ((S₁).algebra.a.2 ⨯ (S₁).substitutionParameters)) :
    (F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
      ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).algebra.a.2)
        ((literalFormulaInputPresentationIso V σ π d).hom.toFun q) =
      (literalFormulaPresentationIso V σ π d).hom.toFun
        ((prod.fst : (S₁).algebra.a.2 ⨯ (S₁).substitutionParameters ⟶ (S₁).algebra.a.2).toFun q) :=
  literalFormulaInput_word V σ π d q

example (p : NumericalTuples.Point (S₁).substitutionParameters) :
    ((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
      (S₀).substitutionParameters (NumericalCoordinates.codedPredicate V))
      ((literalParameterPresentationIso V σ π d).hom.toFun p)).val =
    NumericalTuples.code V.dimension ((prod.fst : (S₁).substitutionParameters ⟶ V).toFun p).val :=
  literalParameter_name_value V σ π d p

end CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralInputValuesChecks
