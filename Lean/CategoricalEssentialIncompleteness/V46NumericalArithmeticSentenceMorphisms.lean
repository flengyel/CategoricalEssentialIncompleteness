/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralNegation
public import CategoricalEssentialIncompleteness.V46NumericalArithmeticCoordinates
public import CategoricalEssentialIncompleteness.V46NumericalSentenceMorphisms

/-! # Arithmetic sentence negation and named numeral substitution on syntax -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SentenceMorphisms
open NamedArithmeticSignature
local notation "S" => Coordinates.numericalSyntax

theorem literalSentence_word (s : NumericalTuples.Point (S).sentenceObject) :
    (Coordinates.literalSentence.toFun s).val =
      NumericalNamed.literalSentenceWord NumericalNamed.variableObject
        Coordinates.functions Coordinates.relations bound s :=
  (Coordinates.literalSentence_value s).trans
    (Coordinates.formulaIso_value ((S).sentenceInclusion.toFun s))

theorem negation_value (s : NumericalTuples.Point (S).sentenceObject) :
    (Coordinates.literalSentence.toFun ((S).sentenceNegation.toFun s)).val =
      NamedArithmeticProofSearch.negationWord ℕ (Coordinates.literalSentence.toFun s).val := by
  have h := NumericalNamed.literal_sentenceNegation_value NumericalNamed.variableObject
    Coordinates.functions Coordinates.relations bound s
  have hc := Algorithms.formulaConstructor_signature (M := ℕ)
    (NumericalCoordinates.codedPredicate NumericalNamed.variableObject) variableSymbols
    (fun n => NumericalCoordinates.codedPredicate (Coordinates.relations n)) relationSymbols bound true
    (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair
      (NumericalNamed.literalSentenceWord NumericalNamed.variableObject
        Coordinates.functions Coordinates.relations bound s) 1) 0) 0)
  exact (literalSentence_word ((S).sentenceNegation.toFun s)).trans
    (h.trans (hc.trans (congrArg (NamedArithmeticProofSearch.negationWord ℕ)
      (literalSentence_word s).symm)))

/-- This square uses the constructed sentence negation itself. -/
theorem negation_literal_square :
    (S).sentenceNegation ≫ Coordinates.literalSentence =
      Coordinates.literalSentence ≫ NumericalSentenceMorphisms.negation := by
  apply NumericalTuples.Map.ext
  funext s
  apply Subtype.ext
  change (Coordinates.literalSentence.toFun ((S).sentenceNegation.toFun s)).val =
    (NumericalSentenceMorphisms.negation.toFun (Coordinates.literalSentence.toFun s)).val
  exact (negation_value s).trans
    (NumericalSentenceMorphisms.negation_value (Coordinates.literalSentence.toFun s)).symm

section GenericSquares
variable {C : Type u} [Category.{v} C]

theorem compose_squares {A B D : C} (f : A ⟶ A) (g : B ⟶ B) (h : D ⟶ D)
    (i : A ⟶ B) (j : B ⟶ D) (hi : f ≫ i = i ≫ g) (hj : g ≫ j = j ≫ h) :
    f ≫ (i ≫ j) = (i ≫ j) ≫ h := by
  rw [← Category.assoc, hi, Category.assoc, hj, Category.assoc]

theorem map_conjugate_hom {D : Type*} [Category D] (F : C ⥤ D)
    {A B : C} (i : A ≅ B) (f : B ⟶ B) :
    F.map (i.hom ≫ f ≫ i.inv) ≫ F.map i.hom = F.map i.hom ≫ F.map f := by
  rw [← F.map_comp]
  have h : (i.hom ≫ f ≫ i.inv) ≫ i.hom = i.hom ≫ f := by
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, F.map_comp]
end GenericSquares

theorem negation_original_chart_square :
    NumericalSentenceMorphisms.negation ≫ numericalInterpretation.map ArithmeticLiteralModel.sentenceChart.hom =
      numericalInterpretation.map ArithmeticLiteralModel.sentenceChart.hom ≫
        numericalInterpretation.map Coordinates.originalSyntax.sentenceNegation :=
  map_conjugate_hom numericalInterpretation ArithmeticLiteralModel.sentenceChart
    Coordinates.originalSyntax.sentenceNegation

theorem negation_square :
    (S).sentenceNegation ≫ Coordinates.sentenceIso.hom =
      Coordinates.sentenceIso.hom ≫ numericalInterpretation.map Coordinates.originalSyntax.sentenceNegation := by
  simpa only [Coordinates.sentenceIso, Iso.trans_hom, asIso_hom, Functor.mapIso_hom,
    Category.assoc] using
      compose_squares (S).sentenceNegation NumericalSentenceMorphisms.negation
        (numericalInterpretation.map Coordinates.originalSyntax.sentenceNegation)
        Coordinates.literalSentence (numericalInterpretation.map ArithmeticLiteralModel.sentenceChart.hom)
        negation_literal_square negation_original_chart_square

/-- Both domains have the literal one-dimensional natural-number coordinates. -/
def omegaDomainIso : NumericalNamed.variableObject ≅ NumericalSentenceMorphisms.omega := Iso.refl _

theorem omegaDomainIso_apply (n : ℕ) :
    omegaDomainIso.hom.toFun (NumericalNamed.variablePoint n) =
      NumericalSentenceMorphisms.omegaPoint n := rfl

theorem omegaDomainIso_variable : omegaDomainIso.hom ≫ NumericalSentenceMorphisms.omegaIso.hom =
    Coordinates.variableIso.hom := by
  exact Category.id_comp _

/-- This is a morphism into the constructed numerical syntax sentence pullback. -/
def theta (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    NumericalNamed.variableObject ⟶ (S).sentenceObject :=
  omegaDomainIso.hom ≫ NumericalSentenceMorphisms.theta φ hφ ≫ (asIso Coordinates.literalSentence).inv

theorem theta_literal (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    theta φ hφ ≫ Coordinates.literalSentence =
      omegaDomainIso.hom ≫ NumericalSentenceMorphisms.theta φ hφ := by
  simp only [theta, Category.assoc, asIso_inv, IsIso.inv_hom_id, Category.comp_id]

theorem theta_sentenceIso (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    theta φ hφ ≫ Coordinates.sentenceIso.hom =
      omegaDomainIso.hom ≫ NumericalSentenceMorphisms.theta φ hφ ≫
        numericalInterpretation.map ArithmeticLiteralModel.sentenceChart.hom := by
  have h := congrArg (fun f => f ≫ numericalInterpretation.map ArithmeticLiteralModel.sentenceChart.hom)
    (theta_literal φ hφ)
  simpa only [Coordinates.sentenceIso, Iso.trans_hom, asIso_hom, Functor.mapIso_hom,
    Category.assoc] using h

theorem theta_value (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (n : ℕ) :
    (Coordinates.literalSentence.toFun ((theta φ hφ).toFun (NumericalNamed.variablePoint n))).val =
      NamedArithmeticFixedSubstitution.value φ n := by
  have h := congrArg (fun f => (f.toFun (NumericalNamed.variablePoint n)).val) (theta_literal φ hφ)
  change (Coordinates.literalSentence.toFun ((theta φ hφ).toFun (NumericalNamed.variablePoint n))).val =
    ((NumericalSentenceMorphisms.theta φ hφ).toFun (NumericalSentenceMorphisms.omegaPoint n)).val at h
  exact h.trans (NumericalSentenceMorphisms.theta_value φ hφ n)

theorem theta_word (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (n : ℕ) :
    NumericalNamed.literalSentenceWord NumericalNamed.variableObject Coordinates.functions Coordinates.relations bound
      ((theta φ hφ).toFun (NumericalNamed.variablePoint n)) = NamedArithmeticFixedSubstitution.value φ n :=
  (literalSentence_word ((theta φ hφ).toFun (NumericalNamed.variablePoint n))).symm.trans
    (theta_value φ hφ n)

theorem standard_literal_result (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (n : ℕ) :
    ∃ out : Formula, φ.substitute 0 (numeral n) = some out ∧
      NumericalNamed.literalSentenceWord NumericalNamed.variableObject Coordinates.functions Coordinates.relations bound
        ((theta φ hφ).toFun (NumericalNamed.variablePoint n)) = formulaCode out ∧ out.freeVariables = [] := by
  obtain ⟨out, hs, hw, hc⟩ := NamedArithmeticFixedSubstitution.standard_literal_result φ hφ n
  exact ⟨out, hs, (theta_word φ hφ n).trans hw, hc⟩

theorem theta_standard_interpretation (φ : Formula)
    (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (n : ℕ) :
    NumericalNamed.literalSentenceWord NumericalNamed.variableObject Coordinates.functions Coordinates.relations bound
      ((theta φ hφ).toFun (NumericalNamed.variablePoint n)) =
      ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map
        (NamedArithmeticLiteralTotal.theta φ hφ)
        (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 ℕ n)).val.val :=
  (theta_word φ hφ n).trans (NamedArithmeticLiteralTotal.canonical_value_at φ hφ ℕ n).symm

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SentenceMorphisms
