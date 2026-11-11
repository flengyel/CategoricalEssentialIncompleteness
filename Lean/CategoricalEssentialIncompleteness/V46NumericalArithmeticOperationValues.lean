/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticCoordinates
public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralInputValues

/-! # The actual arithmetic numerical substitution and admissibility values -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.OperationValues
open Coordinates NamedArithmeticSignature
local notation "S" => numericalSyntax
local notation "S₀" => sourceSyntax
local notation "F" => PredicateInterpretation.functor 𝗧𝗔 ℕ
local notation "V₀" => NumericalCoordinates.codedPredicate NumericalNamed.variableObject
local notation "σ₀" => LiteralSignature.coefficients functionSymbols
local notation "π₀" => LiteralSignature.coefficients relationSymbols

def name (p : NumericalTuples.Point (S).substitutionParameters) : ℕ :=
  ((prod.fst : (S).substitutionParameters ⟶ NumericalNamed.variableObject).toFun p).val

def replacement (p : NumericalTuples.Point (S).substitutionParameters) : ℕ :=
  (termIso.hom.toFun ((prod.snd : (S).substitutionParameters ⟶ (S).algebra.a.1).toFun p)).val

private theorem rechart_projection {A X : NumericalTuples.Object}
    (C D : PredicateCategory 𝗧𝗔)
    (i : X ⟶ NumericalCoordinates.predicateObject C)
    (j : X ⟶ NumericalCoordinates.predicateObject D)
    (h : ∀ x : NumericalTuples.Point X, (i.toFun x).val = (j.toFun x).val)
    (p : A ⟶ X) (q : NumericalTuples.Point A)
    (a : PredicateInterpretation.Obj ℕ D)
    (ha : a = j.toFun (p.toFun q)) : a.val = (i.toFun (p.toFun q)).val :=
  (congrArg Subtype.val ha).trans (h (p.toFun q)).symm

private theorem termInput_name
    (q : NumericalTuples.Point ((S).algebra.a.1 ⨯ (S).substitutionParameters)) :
    ((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (S₀).substitutionParameters V₀)
      ((F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
        ((S₀).algebra.a.1 ⨯ (S₀).substitutionParameters) (S₀).substitutionParameters)
        ((NumericalNamed.literalTermInputPresentationIso
          NumericalNamed.variableObject functions relations bound).hom.toFun q))).val =
      name ((prod.snd : (S).algebra.a.1 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q) := by
  have hp := NumericalNamed.literalTermInput_parameter NumericalNamed.variableObject functions relations bound q
  have hx := NumericalNamed.literalParameter_name_value NumericalNamed.variableObject functions relations bound ((prod.snd : (S).algebra.a.1 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q)
  exact (congrArg (fun p : PredicateInterpretation.Obj ℕ (S₀).substitutionParameters =>
    ((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
      (S₀).substitutionParameters V₀) p).val) hp).trans hx

private theorem termInput_replacement
    (q : NumericalTuples.Point ((S).algebra.a.1 ⨯ (S).substitutionParameters)) :
    ((F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (S₀).substitutionParameters (S₀).algebra.a.1)
      ((F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
        ((S₀).algebra.a.1 ⨯ (S₀).substitutionParameters) (S₀).substitutionParameters)
        ((NumericalNamed.literalTermInputPresentationIso
          NumericalNamed.variableObject functions relations bound).hom.toFun q))).val =
      replacement ((prod.snd : (S).algebra.a.1 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q) := by
  have hp := NumericalNamed.literalTermInput_parameter NumericalNamed.variableObject functions relations bound q
  have ht := NumericalNamed.literalParameter_term NumericalNamed.variableObject functions relations bound
    ((prod.snd : (S).algebra.a.1 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q)
  have ha := (congrArg (fun p : PredicateInterpretation.Obj ℕ (S₀).substitutionParameters =>
    (F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
      (S₀).substitutionParameters (S₀).algebra.a.1) p) hp).trans ht
  exact rechart_projection
    (originalSyntax.algebra.a.1 : PredicateCategory 𝗧𝗔) (S₀).algebra.a.1
    termIso.hom (NumericalNamed.literalTermPresentationIso NumericalNamed.variableObject functions relations bound).hom
    termIso_value ((prod.snd : (S).algebra.a.1 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters) ≫
      (prod.snd : (S).substitutionParameters ⟶ (S).algebra.a.1)) q _ ha

private theorem termInput_word
    (q : NumericalTuples.Point ((S).algebra.a.1 ⨯ (S).substitutionParameters)) :
    ((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
      ((S₀).algebra.a.1 ⨯ (S₀).substitutionParameters) (S₀).algebra.a.1)
        ((NumericalNamed.literalTermInputPresentationIso
          NumericalNamed.variableObject functions relations bound).hom.toFun q)).val =
      (termIso.hom.toFun ((prod.fst : (S).algebra.a.1 ⨯ (S).substitutionParameters ⟶ (S).algebra.a.1).toFun q)).val := by
  exact rechart_projection
    (originalSyntax.algebra.a.1 : PredicateCategory 𝗧𝗔) (S₀).algebra.a.1
    termIso.hom (NumericalNamed.literalTermPresentationIso NumericalNamed.variableObject functions relations bound).hom
    termIso_value (prod.fst : (S).algebra.a.1 ⨯ (S).substitutionParameters ⟶ (S).algebra.a.1) q _
    (NumericalNamed.literalTermInput_word NumericalNamed.variableObject functions relations bound q)

private theorem formulaInput_name
    (q : NumericalTuples.Point ((S).algebra.a.2 ⨯ (S).substitutionParameters)) :
    ((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (S₀).substitutionParameters V₀)
      ((F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
        ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).substitutionParameters)
        ((NumericalNamed.literalFormulaInputPresentationIso
          NumericalNamed.variableObject functions relations bound).hom.toFun q))).val =
      name ((prod.snd : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q) := by
  have hp := NumericalNamed.literalFormulaInput_parameter NumericalNamed.variableObject functions relations bound q
  have hx := NumericalNamed.literalParameter_name_value NumericalNamed.variableObject functions relations bound ((prod.snd : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q)
  exact (congrArg (fun p : PredicateInterpretation.Obj ℕ (S₀).substitutionParameters =>
    ((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
      (S₀).substitutionParameters V₀) p).val) hp).trans hx

private theorem formulaInput_replacement
    (q : NumericalTuples.Point ((S).algebra.a.2 ⨯ (S).substitutionParameters)) :
    ((F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (S₀).substitutionParameters (S₀).algebra.a.1)
      ((F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
        ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).substitutionParameters)
        ((NumericalNamed.literalFormulaInputPresentationIso
          NumericalNamed.variableObject functions relations bound).hom.toFun q))).val =
      replacement ((prod.snd : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q) := by
  have hp := NumericalNamed.literalFormulaInput_parameter NumericalNamed.variableObject functions relations bound q
  have ht := NumericalNamed.literalParameter_term NumericalNamed.variableObject functions relations bound
    ((prod.snd : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q)
  have ha := (congrArg (fun p : PredicateInterpretation.Obj ℕ (S₀).substitutionParameters =>
    (F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
      (S₀).substitutionParameters (S₀).algebra.a.1) p) hp).trans ht
  exact rechart_projection
    (originalSyntax.algebra.a.1 : PredicateCategory 𝗧𝗔) (S₀).algebra.a.1
    termIso.hom (NumericalNamed.literalTermPresentationIso NumericalNamed.variableObject functions relations bound).hom
    termIso_value ((prod.snd : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters) ≫
      (prod.snd : (S).substitutionParameters ⟶ (S).algebra.a.1)) q _ ha

private theorem formulaInput_word
    (q : NumericalTuples.Point ((S).algebra.a.2 ⨯ (S).substitutionParameters)) :
    ((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
      ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).algebra.a.2)
        ((NumericalNamed.literalFormulaInputPresentationIso
          NumericalNamed.variableObject functions relations bound).hom.toFun q)).val =
      (formulaIso.hom.toFun ((prod.fst : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).algebra.a.2).toFun q)).val := by
  exact rechart_projection
    (originalSyntax.algebra.a.2 : PredicateCategory 𝗧𝗔) (S₀).algebra.a.2
    formulaIso.hom (NumericalNamed.literalFormulaPresentationIso NumericalNamed.variableObject functions relations bound).hom
    formulaIso_value (prod.fst : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).algebra.a.2) q _
    (NumericalNamed.literalFormulaInput_word NumericalNamed.variableObject functions relations bound q)

private theorem result_coordinates (x r w x' r' w' : ℕ)
    (hx : x = x') (hr : r = r') (hw : w = w') :
    ConcreteNamedSubstitution.substitutionResult (M := ℕ) V₀ σ₀ π₀ bound x r w =
      ConcreteNamedSubstitution.substitutionResult (M := ℕ) variableSymbols functionSymbols relationSymbols bound x' r' w' := by
  cases hx
  cases hr
  cases hw
  exact Algorithms.substitutionResult_signature (M := ℕ) V₀ variableSymbols σ₀ functionSymbols π₀ relationSymbols bound x r w

private theorem free_for_coordinates (x r w x' r' w' : ℕ)
    (hx : x = x') (hr : r = r') (hw : w = w') :
    ConcreteNamedSubstitution.substitutionFreeFor (M := ℕ) V₀ σ₀ π₀ bound x r w =
      ConcreteNamedSubstitution.substitutionFreeFor (M := ℕ) variableSymbols functionSymbols relationSymbols bound x' r' w' := by
  cases hx
  cases hr
  cases hw
  exact Algorithms.substitutionFreeFor_signature (M := ℕ) V₀ variableSymbols σ₀ functionSymbols π₀ relationSymbols bound x r w

/-- These typed names denote the constructed substitution morphisms. -/
def termSubstitutionArrow : NumericalTuples.Map
    ((S).algebra.a.1 ⨯ (S).substitutionParameters) (S).algebra.a.1 := (S).termSubstitution

def formulaSubstitutionArrow : NumericalTuples.Map
    (S).admissibleSubstitution (S).algebra.a.2 := (S).formulaSubstitution

theorem termSubstitutionArrow_eq : termSubstitutionArrow = (S).termSubstitution := rfl
theorem formulaSubstitutionArrow_eq : formulaSubstitutionArrow = (S).formulaSubstitution := rfl

/-- No extension of the constructor functions beyond their carriers is used. -/
theorem term_substitution_value
    (q : NumericalTuples.Point ((S).algebra.a.1 ⨯ (S).substitutionParameters)) :
    (termIso.hom.toFun (termSubstitutionArrow.toFun q)).val =
      ConcreteNamedSubstitution.substitutionResult (M := ℕ) variableSymbols functionSymbols relationSymbols bound
        (name ((prod.snd : (S).algebra.a.1 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q))
        (replacement ((prod.snd : (S).algebra.a.1 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q))
        (termIso.hom.toFun ((prod.fst : (S).algebra.a.1 ⨯ (S).substitutionParameters ⟶ (S).algebra.a.1).toFun q)).val := by
  have h := NumericalNamed.literal_termSubstitution_value NumericalNamed.variableObject functions relations bound q
  have hv := rechart_projection
    (originalSyntax.algebra.a.1 : PredicateCategory 𝗧𝗔) (S₀).algebra.a.1
    termIso.hom (NumericalNamed.literalTermPresentationIso NumericalNamed.variableObject functions relations bound).hom
    termIso_value termSubstitutionArrow q _ rfl
  exact hv.symm.trans
    (h.trans (result_coordinates _ _ _ _ _ _ (termInput_name q) (termInput_replacement q) (termInput_word q)))

def optionWord (o : NumericalTuples.Point (OptionSyntax.obj (S).algebra.a.2)) : ℕ :=
  ConcreteNamedComparison.optionCode 𝗧𝗔 ℕ (S₀).algebra.a.2
    ((NumericalNamed.literalOptionPresentationIso NumericalNamed.variableObject functions relations bound).hom.toFun o)

/-- The full Option value is compared, so failure and success remain distinct. -/
theorem formula_option_value
    (q : NumericalTuples.Point ((S).algebra.a.2 ⨯ (S).substitutionParameters)) :
    optionWord ((S).formulaSubstitutionOption.toFun q) =
      ConcreteNamedSubstitution.substitutionResult (M := ℕ) variableSymbols functionSymbols relationSymbols bound
        (name ((prod.snd : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q))
        (replacement ((prod.snd : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q))
        (formulaIso.hom.toFun ((prod.fst : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).algebra.a.2).toFun q)).val := by
  have h := NumericalNamed.literal_formulaSubstitutionOption_value NumericalNamed.variableObject functions relations bound q
  exact h.trans (result_coordinates _ _ _ _ _ _ (formulaInput_name q) (formulaInput_replacement q) (formulaInput_word q))

/-- This is the actual admissibility inclusion image and the independent
primitive free-for flag, with the fixed PA arithmetic word coordinates. -/
theorem admissible_iff
    (q : NumericalTuples.Point ((S).algebra.a.2 ⨯ (S).substitutionParameters)) :
    (∃ a, (S).admissibleInclusion.toFun a = q) ↔
      ConcreteNamedSubstitution.substitutionFreeFor (M := ℕ) variableSymbols functionSymbols relationSymbols bound
        (name ((prod.snd : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q))
        (replacement ((prod.snd : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q))
        (formulaIso.hom.toFun ((prod.fst : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).algebra.a.2).toFun q)).val = 1 := by
  have h := NumericalNamed.literal_admissible_iff NumericalNamed.variableObject functions relations bound q
  exact h.trans (Iff.of_eq (congrArg (fun n : ℕ => n = 1)
    (free_for_coordinates _ _ _ _ _ _ (formulaInput_name q) (formulaInput_replacement q) (formulaInput_word q))))

private theorem admissible_input (a : NumericalTuples.Point (S).admissibleSubstitution) :
    (F).map (S₀).admissibleInclusion
      ((NumericalNamed.literalAdmissiblePresentationIso
        NumericalNamed.variableObject functions relations bound).hom.toFun a) =
      (NumericalNamed.literalFormulaInputPresentationIso
        NumericalNamed.variableObject functions relations bound).hom.toFun
        ((S).admissibleInclusion.toFun a) := by
  have h := congrArg (fun f => f.toFun a)
    (NumericalNamed.literal_admissibleInclusion_code_square
      NumericalNamed.variableObject functions relations bound)
  exact (NumericalCoordinates.predicateMap_value (S₀).admissibleInclusion _).symm.trans h.symm

/-- The actual successful substitution result is computed in the same PA
word coordinates, at every point of its constructed admissibility object. -/
theorem formula_substitution_value (a : NumericalTuples.Point (S).admissibleSubstitution) :
    let q := (S).admissibleInclusion.toFun a
    (formulaIso.hom.toFun (formulaSubstitutionArrow.toFun a)).val =
      π₁ (ConcreteNamedSubstitution.substitutionResult (M := ℕ) variableSymbols functionSymbols relationSymbols bound
        (name ((prod.snd : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q))
        (replacement ((prod.snd : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q))
        (formulaIso.hom.toFun ((prod.fst : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).algebra.a.2).toFun q)).val) := by
  let q := (S).admissibleInclusion.toFun a
  have hi := admissible_input a
  have hx := (congrArg (fun t : PredicateInterpretation.Obj ℕ (Limits.prod (C := PredicateCategory 𝗧𝗔) (S₀).algebra.a.2 (S₀).substitutionParameters) =>
    ((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (S₀).substitutionParameters V₀)
      ((F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
        ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).substitutionParameters) t)).val) hi).trans
          (formulaInput_name q)
  have hr := (congrArg (fun t : PredicateInterpretation.Obj ℕ (Limits.prod (C := PredicateCategory 𝗧𝗔) (S₀).algebra.a.2 (S₀).substitutionParameters) =>
    ((F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (S₀).substitutionParameters (S₀).algebra.a.1)
      ((F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
        ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).substitutionParameters) t)).val) hi).trans
          (formulaInput_replacement q)
  have hw := (congrArg (fun t : PredicateInterpretation.Obj ℕ (Limits.prod (C := PredicateCategory 𝗧𝗔) (S₀).algebra.a.2 (S₀).substitutionParameters) =>
    ((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
      ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).algebra.a.2) t).val) hi).trans
        (formulaInput_word q)
  have h := NumericalNamed.literal_formulaSubstitution_value NumericalNamed.variableObject functions relations bound a
  have hv := rechart_projection
    (originalSyntax.algebra.a.2 : PredicateCategory 𝗧𝗔) (S₀).algebra.a.2
    formulaIso.hom (NumericalNamed.literalFormulaPresentationIso NumericalNamed.variableObject functions relations bound).hom
    formulaIso_value formulaSubstitutionArrow a _ rfl
  exact hv.symm.trans
    (h.trans (congrArg (fun n : ℕ => π₁ n) (result_coordinates _ _ _ _ _ _ hx hr hw)))

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.OperationValues
