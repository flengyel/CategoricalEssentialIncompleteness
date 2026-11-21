/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticOmegaComparison

/-! # The numerical source comparison at its TotalSplit type -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticOmegaComparisonChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example : predicateIdem T NamedArithmeticSignature.variableSymbols = ⊤ :=
  ArithmeticOmegaComparison.variables_idempotent T

example : (⟨⟨omegaObject T,⊤⟩⟩ : TotalSplit T) ≅
    (predicateEquivalence T).functor.obj
      (NamedArithmeticSignature.variableSymbols : PredicateCategory T) :=
  ArithmeticOmegaComparison.omegaIso T

end CategoricalEssentialIncompleteness.V46.ArithmeticOmegaComparisonChecks
