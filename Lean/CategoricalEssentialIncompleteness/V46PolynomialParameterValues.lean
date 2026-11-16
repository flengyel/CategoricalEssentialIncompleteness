/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46LaxPolynomialInputs
public import CategoricalEssentialIncompleteness.V46RegularSlices
public import CategoricalEssentialIncompleteness.V46SliceBaseChangeGeometry

/-! # Values of parameterized polynomial inputs with labelled coefficients -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.PolynomialParameterValues
variable {C : Type u} [Category.{v} C] [Regular C] [HasFiniteCoproducts C]
local instance (P : C) : Regular (Over P) := RegularSlices.regular P
variable {I : Type w}

def object (P : C) (c : I → C) (X : C × C) (p : SyntaxPolynomial I) : Over P :=
  (p.mapCoefficients (fun i => constantFamily P (c i))).eval.obj
    (constantFamily P X.1, constantFamily P X.2)

/-- Template labels are retained even when two positions have the same
coefficient object. -/
def comparison (P : C) (c : I → C) (X : C × C) (p : SyntaxPolynomial I) :
    object P c X p ⟶ constantFamily P ((p.mapCoefficients c).eval.obj X) :=
  match p with
  | .term => 𝟙 _
  | .formula => 𝟙 _
  | .coefficient _ => 𝟙 _
  | .unit => constantUnitComparison P
  | .product p q => prod.map (comparison P c X p) (comparison P c X q) ≫
      constantProductComparison P _ _
  | .sum p q => coprod.map (comparison P c X p) (comparison P c X q) ≫
      constantCoproductComparison P _ _

def value (P : C) (c : I → C) (X : C × C) (p : SyntaxPolynomial I) :
    (object P c X p).left ⟶ (p.mapCoefficients c).eval.obj X :=
  (comparison P c X p).left ≫ prod.snd

@[simp] theorem value_term (P : C) (c : I → C) (X : C × C) :
    value P c X .term = (prod.snd : P ⨯ X.1 ⟶ X.1) := by
  simp only [value, comparison, Over.id_left, Category.id_comp]
  rfl

@[simp] theorem value_formula (P : C) (c : I → C) (X : C × C) :
    value P c X .formula = (prod.snd : P ⨯ X.2 ⟶ X.2) := by
  simp only [value, comparison, Over.id_left, Category.id_comp]
  rfl

@[simp] theorem value_coefficient (P : C) (c : I → C) (X : C × C) (i : I) :
    value P c X (.coefficient i) = (prod.snd : P ⨯ c i ⟶ c i) := by
  simp only [value, comparison, Over.id_left, Category.id_comp]
  rfl

omit [HasFiniteCoproducts C] in
private theorem constantProduct_value {P U W : C} {A B : Over P}
    (f : A ⟶ constantFamily P U) (g : B ⟶ constantFamily P W) :
    (prod.map f g ≫ constantProductComparison P U W).left ≫ prod.snd =
      prod.lift ((prod.fst : A ⨯ B ⟶ A).left ≫ f.left ≫ prod.snd)
        ((prod.snd : A ⨯ B ⟶ B).left ≫ g.left ≫ prod.snd) := by
  have hf := congrArg (fun h => h.left ≫ prod.snd) (prod.map_fst f g)
  have hg := congrArg (fun h => h.left ≫ prod.snd) (prod.map_snd f g)
  simp only [Over.comp_left, Category.assoc] at hf hg
  simp only [Over.comp_left, constantProductComparison, Over.homMk_left,
    prod.lift_snd, prod.comp_lift]
  exact congrArg₂ prod.lift hf hg

@[reassoc] theorem value_product_fst (P : C) (c : I → C) (X : C × C)
    (p q : SyntaxPolynomial I) :
    value P c X (.product p q) ≫ prod.fst =
      (prod.fst : object P c X p ⨯ object P c X q ⟶ object P c X p).left ≫
        value P c X p := by
  unfold value
  change ((prod.map _ _ ≫ constantProductComparison P _ _).left ≫ prod.snd) ≫ prod.fst = _
  rw [constantProduct_value, prod.lift_fst]
  rfl

@[reassoc] theorem value_product_snd (P : C) (c : I → C) (X : C × C)
    (p q : SyntaxPolynomial I) :
    value P c X (.product p q) ≫ prod.snd =
      (prod.snd : object P c X p ⨯ object P c X q ⟶ object P c X q).left ≫
        value P c X q := by
  unfold value
  change ((prod.map _ _ ≫ constantProductComparison P _ _).left ≫ prod.snd) ≫ prod.snd = _
  rw [constantProduct_value, prod.lift_snd]
  rfl

@[reassoc] theorem value_sum_inl (P : C) (c : I → C) (X : C × C)
    (p q : SyntaxPolynomial I) :
    (coprod.inl : object P c X p ⟶ object P c X p ⨿ object P c X q).left ≫
      value P c X (.sum p q) = value P c X p ≫ coprod.inl := by
  have hh : coprod.inl ≫ comparison P c X (.sum p q) =
      comparison P c X p ≫ (constantFamilyFunctor P).map coprod.inl := by
    simp [comparison, constantCoproductComparison]
  have hv := congrArg (fun h => h.left ≫
    (prod.snd : P ⨯ ((.sum p q : SyntaxPolynomial I).mapCoefficients c).eval.obj X ⟶ _)) hh
  simp only [Over.comp_left, Category.assoc, constantFamilyFunctor, Over.homMk_left,
    prod.map_snd] at hv
  simpa only [value, object, Category.assoc] using hv

@[reassoc] theorem value_sum_inr (P : C) (c : I → C) (X : C × C)
    (p q : SyntaxPolynomial I) :
    (coprod.inr : object P c X q ⟶ object P c X p ⨿ object P c X q).left ≫
      value P c X (.sum p q) = value P c X q ≫ coprod.inr := by
  have hh : coprod.inr ≫ comparison P c X (.sum p q) =
      comparison P c X q ≫ (constantFamilyFunctor P).map coprod.inr := by
    simp [comparison, constantCoproductComparison]
  have hv := congrArg (fun h => h.left ≫
    (prod.snd : P ⨯ ((.sum p q : SyntaxPolynomial I).mapCoefficients c).eval.obj X ⟶ _)) hh
  simp only [Over.comp_left, Category.assoc, constantFamilyFunctor, Over.homMk_left,
    prod.map_snd] at hv
  simpa only [value, object, Category.assoc] using hv
end CategoricalEssentialIncompleteness.V46.PolynomialParameterValues
