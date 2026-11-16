/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46SyntaxCoefficientMorphisms

/-! # Forward polynomial comparison for changes of parameter -/
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

/-- The product comparison has its forward direction only. Coefficient
morphisms and products are not required to be invertible. -/
def component (F : C ⥤ D) [PreservesFiniteCoproducts F]
    {c : I → C} {d : I → D} (χ : ∀ i, F.obj (c i) ⟶ d i) (p : SyntaxPolynomial I) (X : C × C) :
    F.obj ((p.mapCoefficients c).eval.obj X) ⟶
      (p.mapCoefficients d).eval.obj (F.obj X.1, F.obj X.2) :=
  match p with
  | .term => 𝟙 _
  | .formula => 𝟙 _
  | .coefficient i => χ i
  | .unit => terminalComparison F
  | .product p q => prodComparison F _ _ ≫
      prod.map (component F χ p X) (component F χ q X)
  | .sum p q => inv (coprodComparison F _ _) ≫
      coprod.map (component F χ p X) (component F χ q X)

theorem naturality (p : SyntaxPolynomial I) {X Y : C × C} (k : X ⟶ Y) :
    F.map ((p.mapCoefficients c).eval.map k) ≫ component F χ p Y =
      component F χ p X ≫
        (p.mapCoefficients d).eval.map (F.map k.1, F.map k.2) := by
  induction p with
  | term => simp [component, SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval]
  | formula => simp [component, SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval]
  | coefficient i => simp [component, SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval]
  | unit => simp [component, SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval]
  | product p q hp hq =>
    change F.map (prod.map _ _) ≫ (prodComparison F _ _ ≫ prod.map _ _) =
      (prodComparison F _ _ ≫ prod.map _ _) ≫ prod.map _ _
    rw [← Category.assoc, prodComparison_natural, Category.assoc, prod.map_map, hp, hq]
    simp only [Category.assoc, prod.map_map]
  | sum p q hp hq =>
    change F.map (coprod.map _ _) ≫ (inv (coprodComparison F _ _) ≫ coprod.map _ _) =
      (inv (coprodComparison F _ _) ≫ coprod.map _ _) ≫ coprod.map _ _
    apply (cancel_epi (coprodComparison F _ _)).mp
    rw [← Category.assoc, coprodComparison_natural]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, coprod.map_map]
    rw [hp, hq]

def comparison (p : SyntaxPolynomial I) :
    (p.mapCoefficients c).eval ⋙ F ⟶ (F.prod F) ⋙ (p.mapCoefficients d).eval where
  app := component F χ p
  naturality {_ _} k := naturality F χ p k

def joint (p q : SyntaxPolynomial I) :
    SyntaxPolynomial.jointFunctor (p.mapCoefficients c) (q.mapCoefficients c) ⋙ (F.prod F) ⟶
      (F.prod F) ⋙ SyntaxPolynomial.jointFunctor (p.mapCoefficients d) (q.mapCoefficients d) where
  app X := (component F χ p X, component F χ q X)
  naturality {_ _} k := Prod.ext (naturality F χ p k) (naturality F χ q k)

/-- Recursive carrier morphisms can be appended to the canonical
comparison without imposing a product-preservation assumption. -/
def input (p : SyntaxPolynomial I) (X : C × C) (Y : D × D)
    (k : (F.prod F).obj X ⟶ Y) :
    F.obj ((p.mapCoefficients c).eval.obj X) ⟶ (p.mapCoefficients d).eval.obj Y :=
  component F χ p X ≫ (p.mapCoefficients d).eval.map k

@[reassoc] theorem input_natural (p : SyntaxPolynomial I) {X X' : C × C}
    {Y Y' : D × D} (k : X ⟶ X') (r : (F.prod F).obj X ⟶ Y)
    (s : (F.prod F).obj X' ⟶ Y') (t : Y ⟶ Y')
    (h : (F.prod F).map k ≫ s = r ≫ t) :
    F.map ((p.mapCoefficients c).eval.map k) ≫ input F χ p X' Y' s =
      input F χ p X Y r ≫ (p.mapCoefficients d).eval.map t := by
  change (F.map k.1, F.map k.2) ≫ s = r ≫ t at h
  dsimp only [input]
  rw [← Category.assoc, naturality, Category.assoc, ← Functor.map_comp, h,
    Functor.map_comp, Category.assoc]
end CategoricalEssentialIncompleteness.V46.LaxPolynomialComparison
