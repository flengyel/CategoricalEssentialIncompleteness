/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralValues
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPlainSubstitutionValues

/-! # The numerical substitution square has the literal primitive graph values -/
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

def literalParameterIso : (E).functor.obj (S₀).substitutionParameters ≅ (S₁).substitutionParameters :=
  substitutionParameterIso (E) V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d)

def literalTermInputIso : (E).functor.obj ((S₀).algebra.a.1 ⨯ (S₀).substitutionParameters) ≅
    (S₁).algebra.a.1 ⨯ (S₁).substitutionParameters :=
  SyntaxOptionTransport.productIso (E) (literalTermIso V σ π d) (literalParameterIso V σ π d)

def literalFormulaInputIso : (E).functor.obj ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) ≅
    (S₁).algebra.a.2 ⨯ (S₁).substitutionParameters :=
  SyntaxOptionTransport.productIso (E) (literalFormulaIso V σ π d) (literalParameterIso V σ π d)

def literalTermInputPresentationIso : (S₁).algebra.a.1 ⨯ (S₁).substitutionParameters ≅
    NumericalCoordinates.predicateObject ((S₀).algebra.a.1 ⨯ (S₀).substitutionParameters) :=
  (literalTermInputIso V σ π d).symm ≪≫
    NumericalCoordinates.predicatePresentationIso ((S₀).algebra.a.1 ⨯ (S₀).substitutionParameters)

def literalFormulaInputPresentationIso : (S₁).algebra.a.2 ⨯ (S₁).substitutionParameters ≅
    NumericalCoordinates.predicateObject ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) :=
  (literalFormulaInputIso V σ π d).symm ≪≫
    NumericalCoordinates.predicatePresentationIso ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters)

theorem literal_termSubstitution_code_square :
    (S₁).termSubstitution ≫ (literalTermPresentationIso V σ π d).hom =
      (literalTermInputPresentationIso V σ π d).hom ≫
        NumericalCoordinates.predicateMap (S₀).termSubstitution :=
  conjugate_operation ((E).functor.map (S₀).termSubstitution) (S₁).termSubstitution
    (literalTermInputIso V σ π d) (literalTermIso V σ π d)
    (NumericalCoordinates.predicatePresentationIso ((S₀).algebra.a.1 ⨯ (S₀).substitutionParameters))
    (NumericalCoordinates.predicatePresentationIso (S₀).algebra.a.1)
    ((termSubstitutionComparison_iff (E) V σ π d (S₀) (S₁)
      (literalAlgebraIso V σ π d)).mp (literal_termSubstitution_comparison V σ π d))

def literalOptionPresentationIso : OptionSyntax.obj (S₁).algebra.a.2 ≅
    NumericalCoordinates.predicateObject (OptionSyntax.obj (S₀).algebra.a.2) :=
  (SyntaxOptionTransport.optionIso (E) (literalFormulaIso V σ π d)).symm ≪≫
    NumericalCoordinates.predicatePresentationIso (OptionSyntax.obj (S₀).algebra.a.2)

theorem literal_formulaSubstitutionOption_code_square :
    (S₁).formulaSubstitutionOption ≫ (literalOptionPresentationIso V σ π d).hom =
      (literalFormulaInputPresentationIso V σ π d).hom ≫
        NumericalCoordinates.predicateMap (S₀).formulaSubstitutionOption :=
  conjugate_operation ((E).functor.map (S₀).formulaSubstitutionOption) (S₁).formulaSubstitutionOption
    (literalFormulaInputIso V σ π d)
    (SyntaxOptionTransport.optionIso (E) (literalFormulaIso V σ π d))
    (NumericalCoordinates.predicatePresentationIso ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters))
    (NumericalCoordinates.predicatePresentationIso (OptionSyntax.obj (S₀).algebra.a.2))
    ((formulaSubstitutionOptionComparison_iff (E) V σ π d (S₀) (S₁)
      (literalAlgebraIso V σ π d)).mp (literal_formulaSubstitutionOption_comparison V σ π d))

theorem literal_termSubstitution_value
    (q : NumericalTuples.Point ((S₁).algebra.a.1 ⨯ (S₁).substitutionParameters)) :
    let q₀ := (literalTermInputPresentationIso V σ π d).hom.toFun q
    ((literalTermPresentationIso V σ π d).hom.toFun ((S₁).termSubstitution.toFun q)).val =
      ConcreteNamedSubstitution.substitutionResult (M := ℕ) V₀ σ₀ π₀ d
        (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (S₀).substitutionParameters V₀))
          (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance ((S₀).algebra.a.1 ⨯ (S₀).substitutionParameters) (S₀).substitutionParameters)) q₀)).val
        (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (S₀).substitutionParameters (S₀).algebra.a.1))
          (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance ((S₀).algebra.a.1 ⨯ (S₀).substitutionParameters) (S₀).substitutionParameters)) q₀)).val
        (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance ((S₀).algebra.a.1 ⨯ (S₀).substitutionParameters) (S₀).algebra.a.1)) q₀).val :=
  predicate_operation_value (S₀).termSubstitution (S₁).termSubstitution
    (literalTermInputPresentationIso V σ π d) (literalTermPresentationIso V σ π d)
    (literal_termSubstitution_code_square V σ π d) Subtype.val _
    (ConcreteNamedComparison.plain_termSubstitution_value 𝗧𝗔 V₀ σ₀ π₀ d ℕ) q

theorem literal_formulaSubstitutionOption_value
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
  predicate_operation_value (S₀).formulaSubstitutionOption (S₁).formulaSubstitutionOption
    (literalFormulaInputPresentationIso V σ π d) (literalOptionPresentationIso V σ π d)
    (literal_formulaSubstitutionOption_code_square V σ π d)
    (ConcreteNamedComparison.optionCode 𝗧𝗔 ℕ (S₀).algebra.a.2) _
    (ConcreteNamedComparison.plain_formulaSubstitutionOption_value 𝗧𝗔 V₀ σ₀ π₀ d ℕ) q

end CategoricalEssentialIncompleteness.V46.NumericalNamed
