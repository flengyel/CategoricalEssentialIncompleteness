/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxStableTransport

/-! # Explicit signature checks for StableTransport -/

noncomputable section
universe v₁ v₂ u₁ u₂ w
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticLists.Transport
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Transport
variable {I : Type w} {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) {P : C} {Q : D} (b : E.functor.obj P ≅ Q)
variable (f : I → C) (g : I → D) (χ : ∀ i, E.functor.obj (f i) ≅ g i)

example (p q : SyntaxPolynomial I)
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (p.mapCoefficients f) (q.mapCoefficients f)))
    (h : ∀ R : C, IsInitial (SyntaxPolynomial.algebraWithParameters
      (p.mapCoefficients f) (q.mapCoefficients f) A R)) (R : D) :
    IsInitial (SyntaxPolynomial.algebraWithParameters
      (p.mapCoefficients g) (q.mapCoefficients g) (mappedAlgebra E f g χ p q A) R) :=
  mappedStable E f g χ p q A h R
