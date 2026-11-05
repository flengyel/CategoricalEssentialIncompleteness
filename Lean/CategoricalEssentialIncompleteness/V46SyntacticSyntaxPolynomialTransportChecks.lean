/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPolynomialTransport

/-! # Explicit signature checks for PolynomialTransport -/

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

example (p : SyntaxPolynomial I) :
    ((p.mapCoefficients f).withParameters P).eval ⋙ (sliceEquivalence E b).functor ≅
      ((sliceEquivalence E b).prod (sliceEquivalence E b)).functor ⋙
        ((p.mapCoefficients g).withParameters Q).eval := sliceNaturalIso E b f g χ p
