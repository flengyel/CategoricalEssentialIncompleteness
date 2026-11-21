/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticFiniteDerivationsPowers


/-! # Ordered finite-power points for finite typed derivation trees -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticFiniteDerivations
namespace CategoricalEssentialIncompleteness.V46.SyntacticFiniteDerivations.PowersChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
example (X : PredicateCategory T) (n : ℕ) (xs : Fin n → SyntacticLists.Obj T M X) :
    ∃ p : SyntacticLists.Obj T M (finitePower X n), ∀ k : Fin n,
      (SyntacticLists.F T M).map (SyntacticDerivation.StandardInduction.finiteChild T X n k) p = xs k :=
  powerPoints_exists T M X n xs
end CategoricalEssentialIncompleteness.V46.SyntacticFiniteDerivations.PowersChecks
