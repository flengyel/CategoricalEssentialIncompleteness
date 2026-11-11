/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RecursiveDomainInterpretation
public import CategoricalEssentialIncompleteness.V46UltrapowerComparison

/-! # Arithmetic comparison for the original recursive domain interpretation -/

@[expose] public section

noncomputable section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic Filter CategoryTheory

namespace CategoricalEssentialIncompleteness.V46.ArithmeticUltrapower

variable {I : Type} (U : Ultrafilter I)

/-- The arithmetic-ultrapower comparison on the manuscript's original
recursively interpreted carriers, with literal interpreted-idempotent domains. -/
def recursiveComparison :
    PredicateInterpretation.recursiveDomainFunctor 𝗣𝗔 ℕ ⋙ Ultrapower.functor U ≅
      PredicateInterpretation.recursiveDomainFunctor 𝗣𝗔 (Model U) :=
  Functor.isoWhiskerRight (PredicateInterpretation.recursiveDomainComparison 𝗣𝗔 ℕ)
      (Ultrapower.functor U) ≪≫ canonicalComparison U ≪≫
    (PredicateInterpretation.recursiveDomainComparison 𝗣𝗔 (Model U)).symm

end CategoricalEssentialIncompleteness.V46.ArithmeticUltrapower
