/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPlainTransportData


/-! # Statement checks in `V46ConcreteNamedComparisonPlainTransportDataChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.PlainTransportDataChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)

example : SyntaxOperationsTransport.mappedSyntaxAlgebra
    (CategoryTheory.Equivalence.refl : PredicateCategory T ≌ PredicateCategory T)
    V σ π d (categoricalSyntax T V σ π d) ≅
      (plainCategoricalSyntax T V σ π d).algebra := plainTransportAlgebraIso T V σ π d

example : (categoricalSyntax T V σ π d).termOccurrences =
    (syntaxPlainIso T V σ π d false).hom ≫
      (plainCategoricalSyntax T V σ π d).termOccurrences :=
  plainTransport_termOccurrences T V σ π d

example : (categoricalSyntax T V σ π d).formulaOccurrences =
    (syntaxPlainIso T V σ π d true).hom ≫
      (plainCategoricalSyntax T V σ π d).formulaOccurrences :=
  plainTransport_formulaOccurrences T V σ π d
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.PlainTransportDataChecks
