/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationInitial


/-! # Initiality of the mapped PA constructor algebra -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.Initial
open SyntacticSyntax
example (σ : ℕ → PredicateCategory 𝗣𝗔) (N : ℕ) :
    IsInitial (Projection.mappedJointAlgebra σ N
      (postfixAlgebra 𝗣𝗔 (SyntaxPolynomial.constructors σ N) .unit)) := mappedJointInitial σ N
example (σ : ℕ → PredicateCategory 𝗣𝗔) (N : ℕ) :
    IsInitial (Projection.mappedOneSortAlgebra σ N (oneSortAlgebra 𝗣𝗔 σ N)) := mappedOneSortInitial σ N
end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.Initial
