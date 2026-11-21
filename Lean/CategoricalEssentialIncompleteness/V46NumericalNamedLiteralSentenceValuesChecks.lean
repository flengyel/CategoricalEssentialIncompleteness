/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralSentenceValues


/-! # The numerical sentence pullback has exactly the closed named words -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralSentenceValuesChecks
open NumericalNamed
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)

example (w : NumericalTuples.Point (literalCategoricalSyntax V σ π d).algebra.a.2) :
    (∃ s, (literalCategoricalSyntax V σ π d).sentenceInclusion.toFun s = w) ↔
    ConcreteNamedSubstitution.freeVariables (M := ℕ) (NumericalCoordinates.codedPredicate V)
      (fun n => NumericalCoordinates.codedPredicate (σ n))
      (fun n => NumericalCoordinates.codedPredicate (π n)) d
      ((literalFormulaPresentationIso V σ π d).hom.toFun w).val = 0 :=
  literal_sentence_iff V σ π d w
example (s : NumericalTuples.Point (literalCategoricalSyntax variableObject σ π d).sentenceObject) :
    ∃ φ : NamedFiniteSyntax.Formula
      (NamedPostfixEncoding.Symbols (fun n => NumericalCoordinates.codedPredicate (σ n)))
      (NamedPostfixEncoding.Symbols (fun n => NumericalCoordinates.codedPredicate (π n))) d,
      φ.freeVariables = [] ∧ NamedPostfixEncoding.formulaCode φ =
        ((literalFormulaPresentationIso variableObject σ π d).hom.toFun
          ((literalCategoricalSyntax variableObject σ π d).sentenceInclusion.toFun s)).val :=
  literal_sentence_decodes σ π d s

end CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralSentenceValuesChecks
