/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralConstructorValues
public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralSentenceValues
public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportConstructorsFormula
public import CategoricalEssentialIncompleteness.V46NamedPlainOperationsModels

/-! # The numerical sentence negation in literal word coordinates -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalNamed
open SyntaxOperationsTransport

section SentenceNaturality
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V : D) (σ π : ℕ → D) (d : ℕ)
variable (R₀ : CategoricalSyntax (E.inverse.obj V)
  (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
variable (R₁ : CategoricalSyntax V σ π d)

theorem sentenceNegation_natural (i : E.functor.obj R₀.sentenceObject ≅ R₁.sentenceObject)
    (j : E.functor.obj R₀.algebra.a.2 ≅ R₁.algebra.a.2)
    (hi : E.functor.map R₀.sentenceInclusion ≫ j.hom = i.hom ≫ R₁.sentenceInclusion)
    (hj : E.functor.map R₀.negationConstructor ≫ j.hom = j.hom ≫ R₁.negationConstructor) :
    E.functor.map R₀.sentenceNegation ≫ i.hom = i.hom ≫ R₁.sentenceNegation := by
  apply (cancel_mono R₁.sentenceInclusion).mp
  calc
    (E.functor.map R₀.sentenceNegation ≫ i.hom) ≫ R₁.sentenceInclusion =
        E.functor.map R₀.sentenceNegation ≫ (E.functor.map R₀.sentenceInclusion ≫ j.hom) := by
          rw [Category.assoc, hi]
    _ = E.functor.map (R₀.sentenceNegation ≫ R₀.sentenceInclusion) ≫ j.hom := by
          rw [E.functor.map_comp, Category.assoc]
    _ = E.functor.map (R₀.sentenceInclusion ≫ R₀.negationConstructor) ≫ j.hom := by
          rw [R₀.sentenceNegation_inclusion]
    _ = (E.functor.map R₀.sentenceInclusion ≫ j.hom) ≫ R₁.negationConstructor := by
          rw [E.functor.map_comp, Category.assoc, hj, Category.assoc]
    _ = (i.hom ≫ R₁.sentenceNegation) ≫ R₁.sentenceInclusion := by
          simp only [hi, Category.assoc, R₁.sentenceNegation_inclusion]
end SentenceNaturality

section PresentedNegation
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
variable (R₀ : CategoricalSyntax (literalEquivalence.inverse.obj V)
  (fun n => literalEquivalence.inverse.obj (σ n))
  (fun n => literalEquivalence.inverse.obj (π n)) d)
variable (R₁ : CategoricalSyntax V σ π d)
variable (c : mappedSyntaxAlgebra literalEquivalence V σ π d R₀ ≅ R₁.algebra)

theorem presentedNegationConstructor_square :
    R₁.negationConstructor ≫ (presentedFormulaConstructorOutputIso V σ π d R₀ R₁ c).hom =
      (presentedFormulaConstructorOutputIso V σ π d R₀ R₁ c).hom ≫
        NumericalCoordinates.predicateMap R₀.negationConstructor :=
  conjugate_operation (literalEquivalence.functor.map R₀.negationConstructor)
    R₁.negationConstructor (syntaxFormulaIso («S₁» := R₁) literalEquivalence V σ π d R₀ c)
    (syntaxFormulaIso («S₁» := R₁) literalEquivalence V σ π d R₀ c)
    (NumericalCoordinates.predicatePresentationIso R₀.algebra.a.2)
    (NumericalCoordinates.predicatePresentationIso R₀.algebra.a.2)
    (syntax_negation_constructor literalEquivalence V σ π d R₀ R₁ c)

theorem presentedNegationConstructor_value {Z : Type}
    (value : PredicateInterpretation.Obj ℕ R₀.algebra.a.2 → Z)
    (output : PredicateInterpretation.Obj ℕ R₀.algebra.a.2 → Z)
    (hsource : ∀ a, value ((PredicateInterpretation.functor 𝗧𝗔 ℕ).map R₀.negationConstructor a) = output a)
    (x : NumericalTuples.Point R₁.algebra.a.2) :
    value ((presentedFormulaConstructorOutputIso V σ π d R₀ R₁ c).hom.toFun
      (R₁.negationConstructor.toFun x)) =
      output ((presentedFormulaConstructorOutputIso V σ π d R₀ R₁ c).hom.toFun x) :=
  predicate_operation_value R₀.negationConstructor R₁.negationConstructor
    (presentedFormulaConstructorOutputIso V σ π d R₀ R₁ c)
    (presentedFormulaConstructorOutputIso V σ π d R₀ R₁ c)
    (presentedNegationConstructor_square V σ π d R₀ R₁ c) value output hsource x

theorem presentedSentenceNegation_square
    (i : literalEquivalence.functor.obj R₀.sentenceObject ≅ R₁.sentenceObject)
    (hi : literalEquivalence.functor.map R₀.sentenceInclusion ≫
      (syntaxFormulaIso («S₁» := R₁) literalEquivalence V σ π d R₀ c).hom =
        i.hom ≫ R₁.sentenceInclusion) :
    R₁.sentenceNegation ≫ (i.symm ≪≫ NumericalCoordinates.predicatePresentationIso R₀.sentenceObject).hom =
      (i.symm ≪≫ NumericalCoordinates.predicatePresentationIso R₀.sentenceObject).hom ≫
        NumericalCoordinates.predicateMap R₀.sentenceNegation :=
  conjugate_operation (literalEquivalence.functor.map R₀.sentenceNegation)
    R₁.sentenceNegation i i
    (NumericalCoordinates.predicatePresentationIso R₀.sentenceObject)
    (NumericalCoordinates.predicatePresentationIso R₀.sentenceObject)
    (sentenceNegation_natural literalEquivalence V σ π d R₀ R₁ i
      (syntaxFormulaIso («S₁» := R₁) literalEquivalence V σ π d R₀ c) hi
      (syntax_negation_constructor literalEquivalence V σ π d R₀ R₁ c))
end PresentedNegation

section SentenceWords
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
variable (S : CategoricalSyntax V σ π d) (C : PredicateCategory 𝗧𝗔)
variable (j : S.algebra.a.2 ≅ NumericalCoordinates.predicateObject C)

def syntaxSentenceWord (s : NumericalTuples.Point S.sentenceObject) : ℕ :=
  (j.hom.toFun (S.sentenceInclusion.toFun s)).val

theorem syntaxSentenceWord_negation (wordNegation : ℕ → ℕ)
    (hneg : ∀ φ : NumericalTuples.Point S.algebra.a.2,
      (j.hom.toFun (S.negationConstructor.toFun φ)).val = wordNegation (j.hom.toFun φ).val)
    (s : NumericalTuples.Point S.sentenceObject) :
    syntaxSentenceWord V σ π d S C j (S.sentenceNegation.toFun s) =
      wordNegation (syntaxSentenceWord V σ π d S C j s) := by
  have h := congrArg (fun f => f.toFun s) S.sentenceNegation_inclusion
  change S.sentenceInclusion.toFun (S.sentenceNegation.toFun s) =
    S.negationConstructor.toFun (S.sentenceInclusion.toFun s) at h
  exact (congrArg (fun φ => (j.hom.toFun φ).val) h).trans
    (hneg (S.sentenceInclusion.toFun s))
end SentenceWords

section LiteralNegation
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "E" => literalEquivalence
local notation "S₀" => literalSourceSyntax V σ π d
local notation "S₁" => literalCategoricalSyntax V σ π d
local notation "V₀" => NumericalCoordinates.codedPredicate V
local notation "σ₀" => (fun n => NumericalCoordinates.codedPredicate (σ n))
local notation "π₀" => (fun n => NumericalCoordinates.codedPredicate (π n))

abbrev literal_negationConstructor_code_square :=
  presentedNegationConstructor_square V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d)

abbrev literal_sentenceNegation_comparison :=
  sentenceNegation_natural (E) V σ π d (S₀) (S₁)
    (literalSentenceIso V σ π d) (literalFormulaIso V σ π d)
    (literalSentenceIso_inclusion V σ π d).symm
    (syntax_negation_constructor (E) V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d))

abbrev literal_sentenceNegation_code_square :=
  presentedSentenceNegation_square V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d)
    (literalSentenceIso V σ π d) (literalSentenceIso_inclusion V σ π d).symm

def literalSentenceWord :=
  syntaxSentenceWord V σ π d (S₁) (S₀).algebra.a.2 (literalFormulaPresentationIso V σ π d)

theorem literal_negationConstructor_value (φ : NumericalTuples.Point (S₁).algebra.a.2) :
    ((literalFormulaPresentationIso V σ π d).hom.toFun ((S₁).negationConstructor.toFun φ)).val =
      SyntacticSyntax.Coding.constructor (M := ℕ) true
        (SyntaxPolynomial.formulaExpression V₀ π₀ d)
        (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair
          ((literalFormulaPresentationIso V σ π d).hom.toFun φ).val 1) 0) 0) :=
  presentedNegationConstructor_value V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d) Subtype.val _
    (NamedPlainOperationsModels.negation_value 𝗧𝗔 ℕ V₀ σ₀ π₀ d) φ

theorem literal_sentenceNegation_value (s : NumericalTuples.Point (S₁).sentenceObject) :
    literalSentenceWord V σ π d ((S₁).sentenceNegation.toFun s) =
      SyntacticSyntax.Coding.constructor (M := ℕ) true
        (SyntaxPolynomial.formulaExpression V₀ π₀ d)
        (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair
          (literalSentenceWord V σ π d s) 1) 0) 0) :=
  syntaxSentenceWord_negation V σ π d (S₁) (S₀).algebra.a.2
    (literalFormulaPresentationIso V σ π d)
    (fun word : ℕ => SyntacticSyntax.Coding.constructor (M := ℕ) true
      (SyntaxPolynomial.formulaExpression V₀ π₀ d)
      (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair word 1) 0) 0))
    (literal_negationConstructor_value V σ π d) s

theorem literal_sentenceNegation_formulaCode
    (s : NumericalTuples.Point (literalCategoricalSyntax variableObject σ π d).sentenceObject) :
    ∃ φ : NamedFiniteSyntax.Formula (NamedPostfixEncoding.Symbols σ₀)
        (NamedPostfixEncoding.Symbols π₀) d,
      φ.freeVariables = [] ∧ literalSentenceWord variableObject σ π d s = NamedPostfixEncoding.formulaCode φ ∧
        literalSentenceWord variableObject σ π d
          ((literalCategoricalSyntax variableObject σ π d).sentenceNegation.toFun s) =
            NamedPostfixEncoding.formulaCode (.neg φ) := by
  obtain ⟨φ, hc, hw⟩ := literal_sentence_decodes σ π d s
  have hw' : literalSentenceWord variableObject σ π d s = NamedPostfixEncoding.formulaCode φ := hw.symm
  refine ⟨φ, hc, hw', ?_⟩
  have h := literal_sentenceNegation_value variableObject σ π d s
  rw [hw'] at h
  exact h.trans (formula_constructor_variable_parameter (M := ℕ)
    (NumericalCoordinates.codedPredicate variableObject) NamedPostfixEncoding.variableCarrier π₀ d
    (NamedPostfixEncoding.negInput (NamedPostfixEncoding.formulaCode φ)))
end LiteralNegation

end CategoricalEssentialIncompleteness.V46.NumericalNamed
