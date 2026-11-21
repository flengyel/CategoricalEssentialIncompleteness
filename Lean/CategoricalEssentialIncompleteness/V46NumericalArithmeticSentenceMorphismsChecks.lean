/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticSentenceMorphisms


/-! # Arithmetic sentence negation and named numeral substitution on syntax -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SentenceMorphismsChecks
open NamedArithmeticSignature SentenceMorphisms

example : Coordinates.numericalSyntax.sentenceNegation ≫ Coordinates.literalSentence =
    Coordinates.literalSentence ≫ NumericalSentenceMorphisms.negation := negation_literal_square

example : Coordinates.numericalSyntax.sentenceNegation ≫ Coordinates.sentenceIso.hom =
    Coordinates.sentenceIso.hom ≫ numericalInterpretation.map Coordinates.originalSyntax.sentenceNegation := negation_square

example (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    NumericalNamed.variableObject ⟶ Coordinates.numericalSyntax.sentenceObject := theta φ hφ

example (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    theta φ hφ ≫ Coordinates.literalSentence =
    omegaDomainIso.hom ≫ NumericalSentenceMorphisms.theta φ hφ := theta_literal φ hφ

example (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (n : ℕ) :
    ∃ out : Formula, φ.substitute 0 (numeral n) = some out ∧
      NumericalNamed.literalSentenceWord NumericalNamed.variableObject Coordinates.functions Coordinates.relations bound
        ((theta φ hφ).toFun (NumericalNamed.variablePoint n)) = formulaCode out ∧ out.freeVariables = [] :=
  standard_literal_result φ hφ n

example (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (n : ℕ) :
    NumericalNamed.literalSentenceWord NumericalNamed.variableObject Coordinates.functions Coordinates.relations bound
      ((theta φ hφ).toFun (NumericalNamed.variablePoint n)) =
      ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map
        (NamedArithmeticLiteralTotal.theta φ hφ)
        (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 ℕ n)).val.val :=
  theta_standard_interpretation φ hφ n

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SentenceMorphismsChecks
