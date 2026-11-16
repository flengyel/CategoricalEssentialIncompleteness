/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46SyntaxPolynomialTransport

/-! # Polynomial action on arbitrary coefficient morphisms -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxCoefficientMorphisms
variable {I : Type w} {C : Type u} [Category.{v} C]
variable [HasFiniteProducts C] [HasFiniteCoproducts C]
variable {c d e : I → C} (h : ∀ i, c i ⟶ d i)

def component {c d : I → C} (h : ∀ i, c i ⟶ d i) (p : SyntaxPolynomial I) (X : C × C) :
    (p.mapCoefficients c).eval.obj X ⟶ (p.mapCoefficients d).eval.obj X :=
  match p with
  | .term => 𝟙 _
  | .formula => 𝟙 _
  | .coefficient i => h i
  | .unit => 𝟙 _
  | .product p q => prod.map (component h p X) (component h q X)
  | .sum p q => coprod.map (component h p X) (component h q X)

theorem naturality (p : SyntaxPolynomial I) {X Y : C × C} (f : X ⟶ Y) :
    (p.mapCoefficients c).eval.map f ≫ component h p Y =
      component h p X ≫ (p.mapCoefficients d).eval.map f := by
  induction p with
  | term => simp [component, SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval]
  | formula => simp [component, SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval]
  | coefficient i => simp [component, SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval]
  | unit => simp [component, SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval]
  | product p q hp hq =>
    change prod.map _ _ ≫ prod.map _ _ = prod.map _ _ ≫ prod.map _ _
    rw [prod.map_map, prod.map_map, hp, hq]
  | sum p q hp hq =>
    change coprod.map _ _ ≫ coprod.map _ _ = coprod.map _ _ ≫ coprod.map _ _
    rw [coprod.map_map, coprod.map_map, hp, hq]

def action (p : SyntaxPolynomial I) : (p.mapCoefficients c).eval ⟶
    (p.mapCoefficients d).eval where
  app := component h p
  naturality {_ _} f := naturality h p f

@[simp] theorem component_id (p : SyntaxPolynomial I) (X : C × C) :
    component (fun i => 𝟙 (c i)) p X = 𝟙 _ := by
  induction p with
  | term => rfl
  | formula => rfl
  | coefficient => rfl
  | unit => rfl
  | product p q hp hq =>
    simp only [component, hp, hq, prod.map_id_id]
    rfl
  | sum p q hp hq =>
    simp only [component, hp, hq, coprod.map_id_id]
    rfl

@[simp] theorem component_comp (g : ∀ i, d i ⟶ e i) (p : SyntaxPolynomial I) (X : C × C) :
    component (fun i => h i ≫ g i) p X = component h p X ≫ component g p X := by
  induction p with
  | term => simp [component]
  | formula => simp [component]
  | coefficient => rfl
  | unit => simp [component]
  | product p q hp hq => simp only [component, hp, hq, prod.map_map]
  | sum p q hp hq => simp only [component, hp, hq, coprod.map_map]

def jointAction (p q : SyntaxPolynomial I) :
    SyntaxPolynomial.jointFunctor (p.mapCoefficients c) (q.mapCoefficients c) ⟶
      SyntaxPolynomial.jointFunctor (p.mapCoefficients d) (q.mapCoefficients d) where
  app X := (component h p X, component h q X)
  naturality {_ _} f := Prod.ext (naturality h p f) (naturality h q f)

end CategoricalEssentialIncompleteness.V46.SyntaxCoefficientMorphisms
