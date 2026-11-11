/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParameterTransport

/-! # Explicit signature checks for ParameterTransport -/

@[expose] public section

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

example (p : SyntaxPolynomial I) (X : C × C) :
    (parameterComponent E b f g χ p X).hom ≫
      SyntaxPolynomial.parameterComparison Q ((E.prod E).functor.obj X) (p.mapCoefficients g) =
    (sliceEquivalence E b).functor.map
      (SyntaxPolynomial.parameterComparison P X (p.mapCoefficients f)) ≫
        (familyComparison E b ((p.mapCoefficients f).eval.obj X)).hom ≫
          (constantFamilyFunctor Q).map (SyntaxPolynomialTransport.component E f g χ p X).hom :=
  parameterComponent_comparison E b f g χ p X
