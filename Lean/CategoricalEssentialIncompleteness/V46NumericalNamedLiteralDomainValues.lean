/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralSubstitutionValues
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPlainAdmissibleValues
public import CategoricalEssentialIncompleteness.V46NumericalUnderlying

/-! # The numerical substitution domain is the independent free-for flag -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalNamed

abbrev numericalPoints := NumericalUnderlying.functor

theorem numerical_image_chart {A B X Y : NumericalTuples.Object}
    (f : A ⟶ B) (g : X ⟶ Y) (i : A ≅ X) (j : B ≅ Y)
    (hf : f ≫ j.hom = i.hom ≫ g) (b : NumericalTuples.Point B) :
    (∃ a, f.toFun a = b) ↔ ∃ x, g.toFun x = j.hom.toFun b := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨i.hom.toFun a, ?_⟩
    exact (congrArg (fun h => h.toFun a) hf).symm.trans (congrArg j.hom.toFun ha)
  · rintro ⟨x, hx⟩
    refine ⟨i.inv.toFun x, (numericalPoints.mapIso j).toEquiv.injective ?_⟩
    exact (congrArg (fun h => h.toFun (i.inv.toFun x)) hf).trans
      ((congrArg g.toFun ((numericalPoints.mapIso i).toEquiv.apply_symm_apply x)).trans hx)

variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "E" => literalEquivalence
local notation "S₀" => literalSourceSyntax V σ π d
local notation "S₁" => literalCategoricalSyntax V σ π d
local notation "V₀" => NumericalCoordinates.codedPredicate V
local notation "σ₀" => (fun n => NumericalCoordinates.codedPredicate (σ n))
local notation "π₀" => (fun n => NumericalCoordinates.codedPredicate (π n))

def literalAdmissiblePresentationIso : (S₁).admissibleSubstitution ≅
    NumericalCoordinates.predicateObject (S₀).admissibleSubstitution :=
  (literalAdmissibleIso V σ π d).symm ≪≫
    NumericalCoordinates.predicatePresentationIso (S₀).admissibleSubstitution

theorem literal_admissibleInclusion_code_square :
    (S₁).admissibleInclusion ≫ (literalFormulaInputPresentationIso V σ π d).hom =
      (literalAdmissiblePresentationIso V σ π d).hom ≫
        NumericalCoordinates.predicateMap (S₀).admissibleInclusion :=
  conjugate_operation ((E).functor.map (S₀).admissibleInclusion) (S₁).admissibleInclusion
    (literalAdmissibleIso V σ π d) (literalFormulaInputIso V σ π d)
    (NumericalCoordinates.predicatePresentationIso (S₀).admissibleSubstitution)
    (NumericalCoordinates.predicatePresentationIso ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters))
    (literalAdmissibleIso_inclusion V σ π d).symm

theorem literal_formulaSubstitution_code_square :
    (S₁).formulaSubstitution ≫ (literalFormulaPresentationIso V σ π d).hom =
      (literalAdmissiblePresentationIso V σ π d).hom ≫
        NumericalCoordinates.predicateMap (S₀).formulaSubstitution :=
  conjugate_operation ((E).functor.map (S₀).formulaSubstitution) (S₁).formulaSubstitution
    (literalAdmissibleIso V σ π d) (literalFormulaIso V σ π d)
    (NumericalCoordinates.predicatePresentationIso (S₀).admissibleSubstitution)
    (NumericalCoordinates.predicatePresentationIso (S₀).algebra.a.2)
    (literalAdmissibleIso_result V σ π d).symm

theorem literal_admissible_iff
    (q : NumericalTuples.Point ((S₁).algebra.a.2 ⨯ (S₁).substitutionParameters)) :
    let q₀ := (literalFormulaInputPresentationIso V σ π d).hom.toFun q
    (∃ a, (S₁).admissibleInclusion.toFun a = q) ↔
      ConcreteNamedSubstitution.substitutionFreeFor (M := ℕ) V₀ σ₀ π₀ d
        (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (S₀).substitutionParameters V₀))
          (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).substitutionParameters)) q₀)).val
        (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (S₀).substitutionParameters (S₀).algebra.a.1))
          (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).substitutionParameters)) q₀)).val
        (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).algebra.a.2)) q₀).val = 1 := by
  refine (numerical_image_chart (S₁).admissibleInclusion
    (NumericalCoordinates.predicateMap (S₀).admissibleInclusion)
    (literalAdmissiblePresentationIso V σ π d) (literalFormulaInputPresentationIso V σ π d)
    (literal_admissibleInclusion_code_square V σ π d) q).trans ?_
  have hp := ConcreteNamedComparison.plain_admissible_model_iff 𝗧𝗔 V₀ σ₀ π₀ d ℕ
    ((literalFormulaInputPresentationIso V σ π d).hom.toFun q)
  constructor
  · rintro ⟨x, hx⟩
    exact hp.mp ⟨x, (NumericalCoordinates.predicateMap_value (S₀).admissibleInclusion x).symm.trans hx⟩
  · intro h
    obtain ⟨x, hx⟩ := hp.mpr h
    exact ⟨x, (NumericalCoordinates.predicateMap_value (S₀).admissibleInclusion x).trans hx⟩

/-- At an admissibility point the primitive successful result is the value of the
categorical substitution morphism. No flag premise is added. -/
theorem literal_formulaSubstitution_value (a : NumericalTuples.Point (S₁).admissibleSubstitution) :
    let a₀ := (literalAdmissiblePresentationIso V σ π d).hom.toFun a
    let q₀ := (PredicateInterpretation.functor 𝗧𝗔 ℕ).map (S₀).admissibleInclusion a₀
    ((literalFormulaPresentationIso V σ π d).hom.toFun ((S₁).formulaSubstitution.toFun a)).val =
      π₁ (ConcreteNamedSubstitution.substitutionResult (M := ℕ) V₀ σ₀ π₀ d
        (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (S₀).substitutionParameters V₀))
          (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).substitutionParameters)) q₀)).val
        (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (S₀).substitutionParameters (S₀).algebra.a.1))
          (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).substitutionParameters)) q₀)).val
        (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).algebra.a.2)) q₀).val) :=
  predicate_operation_value (S₀).formulaSubstitution (S₁).formulaSubstitution
    (literalAdmissiblePresentationIso V σ π d) (literalFormulaPresentationIso V σ π d)
    (literal_formulaSubstitution_code_square V σ π d) Subtype.val _
    (ConcreteNamedComparison.plain_formulaSubstitution_value 𝗧𝗔 V₀ σ₀ π₀ d ℕ) a

end CategoricalEssentialIncompleteness.V46.NumericalNamed
