/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxPolynomialNormalization


/-! # Explicit normalization of polynomial comparison isomorphisms -/

@[expose] public section
noncomputable section
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxPolynomialNormalizationChecks
open SyntaxOperationsTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (A : C × C) (B : D × D) (i : (E.prod E).functor.obj A ≅ B)
example (p q : SyntaxPolynomial D) (p₀ q₀ : SyntaxPolynomial C) (p₁ q₁ : SyntaxPolynomial D)
    (hp₀ : p₀ = p.mapCoefficients E.inverse.obj) (hq₀ : q₀ = q.mapCoefficients E.inverse.obj)
    (hp₁ : p.mapCoefficients id = p₁) (hq₁ : q.mapCoefficients id = q₁) :
    (normalizedPolynomialIso E A B i (.product p q) (.product p₀ q₀) (.product p₁ q₁)
      (congrArg₂ SyntaxPolynomial.product hp₀ hq₀) (congrArg₂ SyntaxPolynomial.product hp₁ hq₁)).hom =
      (SyntaxOptionTransport.productIso E
        (normalizedPolynomialIso E A B i p p₀ p₁ hp₀ hp₁)
        (normalizedPolynomialIso E A B i q q₀ q₁ hq₀ hq₁)).hom :=
  normalizedPolynomialIso_product E A B i p q p₀ q₀ p₁ q₁ hp₀ hq₀ hp₁ hq₁
example (p q : SyntaxPolynomial D) (p₀ q₀ : SyntaxPolynomial C) (p₁ q₁ : SyntaxPolynomial D)
    (hp₀ : p₀ = p.mapCoefficients E.inverse.obj) (hq₀ : q₀ = q.mapCoefficients E.inverse.obj)
    (hp₁ : p.mapCoefficients id = p₁) (hq₁ : q.mapCoefficients id = q₁) :
    (normalizedPolynomialIso E A B i (.sum p q) (.sum p₀ q₀) (.sum p₁ q₁)
      (congrArg₂ SyntaxPolynomial.sum hp₀ hq₀) (congrArg₂ SyntaxPolynomial.sum hp₁ hq₁)).hom =
      inv (coprodComparison E.functor (p₀.eval.obj A) (q₀.eval.obj A)) ≫
        coprod.map (normalizedPolynomialIso E A B i p p₀ p₁ hp₀ hp₁).hom
          (normalizedPolynomialIso E A B i q q₀ q₁ hq₀ hq₁).hom :=
  normalizedPolynomialIso_sum E A B i p q p₀ q₀ p₁ q₁ hp₀ hq₀ hp₁ hq₁
end CategoricalEssentialIncompleteness.V46.SyntaxPolynomialNormalizationChecks
