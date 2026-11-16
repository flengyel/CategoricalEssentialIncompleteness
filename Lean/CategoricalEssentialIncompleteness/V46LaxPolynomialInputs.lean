/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46LaxPolynomialComparison

/-! # Product projections and coproduct branches of polynomial inputs -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.LaxPolynomialComparison
variable {I : Type w} {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]
variable [HasFiniteProducts C] [HasFiniteCoproducts C]
variable [HasFiniteProducts D] [HasFiniteCoproducts D]
variable (F : C ⥤ D) [PreservesFiniteCoproducts F]
variable {c : I → C} {d : I → D} (χ : ∀ i, F.obj (c i) ⟶ d i)
variable (p q : SyntaxPolynomial I) (X : C × C) (Y : D × D)
variable (k : (F.prod F).obj X ⟶ Y)

@[reassoc] theorem input_product_fst :
    input F χ (.product p q) X Y k ≫ prod.fst =
      F.map prod.fst ≫ input F χ p X Y k := by
  dsimp only [input, component, SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval,
    SyntaxPolynomial.productFunctor]
  simp only [Category.assoc, prod.map_fst, prod.map_fst_assoc, prodComparison_fst_assoc]

@[reassoc] theorem input_product_snd :
    input F χ (.product p q) X Y k ≫ prod.snd =
      F.map prod.snd ≫ input F χ q X Y k := by
  dsimp only [input, component, SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval,
    SyntaxPolynomial.productFunctor]
  simp only [Category.assoc, prod.map_snd, prod.map_snd_assoc, prodComparison_snd_assoc]

@[reassoc] theorem input_sum_inl :
    F.map coprod.inl ≫ input F χ (.sum p q) X Y k =
      input F χ p X Y k ≫ coprod.inl := by
  dsimp only [input, component, SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval,
    SyntaxPolynomial.sumFunctor]
  rw [← Category.assoc, ← Category.assoc, map_inl_inv_coprodComparison,
    coprod.inl_map, Category.assoc, coprod.inl_map]
  exact (Category.assoc _ _ _).symm

@[reassoc] theorem input_sum_inr :
    F.map coprod.inr ≫ input F χ (.sum p q) X Y k =
      input F χ q X Y k ≫ coprod.inr := by
  dsimp only [input, component, SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval,
    SyntaxPolynomial.sumFunctor]
  rw [← Category.assoc, ← Category.assoc, map_inr_inv_coprodComparison,
    coprod.inr_map, Category.assoc, coprod.inr_map]
  exact (Category.assoc _ _ _).symm
end CategoricalEssentialIncompleteness.V46.LaxPolynomialComparison
