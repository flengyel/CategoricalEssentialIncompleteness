/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46PolynomialParameterValues

/-! # Parameter and coefficient changes commute with polynomial values -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.PolynomialParameterSquares
open PolynomialParameterValues
variable {C : Type u} [Category.{v} C] [Regular C] [HasFiniteCoproducts C]
local instance (P : C) : Regular (Over P) := RegularSlices.regular P
variable {I : Type w} {c d : I → C} {P Q : C}

def familyMap (b : P ⟶ Q) {X Y : C} (f : X ⟶ Y) :
    (Over.map b).obj (constantFamily P X) ⟶ constantFamily Q Y :=
  Over.homMk (prod.map b f) (by simp [constantFamily])

omit [HasFiniteCoproducts C] in
@[reassoc] theorem familyMap_value (b : P ⟶ Q) {X Y : C} (f : X ⟶ Y) :
    (familyMap b f).left ≫ prod.snd = prod.snd ≫ f := prod.map_snd _ _

variable (b : P ⟶ Q) (h : ∀ i, c i ⟶ d i) (X Y : C × C) (k : X ⟶ Y)

def baseInput (p : SyntaxPolynomial I) :
    (p.mapCoefficients c).eval.obj X ⟶ (p.mapCoefficients d).eval.obj Y :=
  SyntaxCoefficientMorphisms.component h p X ≫ (p.mapCoefficients d).eval.map k

def relativeInput (p : SyntaxPolynomial I) :
    (Over.map b).obj (object P c X p) ⟶ object Q d Y p :=
  LaxPolynomialComparison.input (Over.map b) (fun i => familyMap b (h i)) p
    (constantFamily P X.1, constantFamily P X.2)
    (constantFamily Q Y.1, constantFamily Q Y.2)
    (familyMap b k.1, familyMap b k.2)

@[reassoc] theorem baseInput_product_fst (p q : SyntaxPolynomial I) :
    baseInput h X Y k (.product p q) ≫ prod.fst =
      prod.fst ≫ baseInput h X Y k p := by
  dsimp [baseInput, SyntaxCoefficientMorphisms.component, SyntaxPolynomial.mapCoefficients,
    SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor]
  simp only [Category.assoc, prod.map_fst, prod.map_fst_assoc]

@[reassoc] theorem baseInput_product_snd (p q : SyntaxPolynomial I) :
    baseInput h X Y k (.product p q) ≫ prod.snd =
      prod.snd ≫ baseInput h X Y k q := by
  dsimp [baseInput, SyntaxCoefficientMorphisms.component, SyntaxPolynomial.mapCoefficients,
    SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor]
  simp only [Category.assoc, prod.map_snd, prod.map_snd_assoc]

@[reassoc] theorem baseInput_sum_inl (p q : SyntaxPolynomial I) :
    coprod.inl ≫ baseInput h X Y k (.sum p q) =
      baseInput h X Y k p ≫ coprod.inl := by
  dsimp [baseInput, SyntaxCoefficientMorphisms.component, SyntaxPolynomial.mapCoefficients,
    SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor]
  rw [← Category.assoc, coprod.inl_map, Category.assoc, coprod.inl_map]
  exact (Category.assoc _ _ _).symm

@[reassoc] theorem baseInput_sum_inr (p q : SyntaxPolynomial I) :
    coprod.inr ≫ baseInput h X Y k (.sum p q) =
      baseInput h X Y k q ≫ coprod.inr := by
  dsimp [baseInput, SyntaxCoefficientMorphisms.component, SyntaxPolynomial.mapCoefficients,
    SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor]
  rw [← Category.assoc, coprod.inr_map, Category.assoc, coprod.inr_map]
  exact (Category.assoc _ _ _).symm

@[reassoc] theorem relativeInput_product_fst (p q : SyntaxPolynomial I) :
    (relativeInput b h X Y k (.product p q)).left ≫
        (prod.fst : object Q d Y p ⨯ object Q d Y q ⟶ object Q d Y p).left =
      (prod.fst : object P c X p ⨯ object P c X q ⟶ object P c X p).left ≫
        (relativeInput b h X Y k p).left :=
  congrArg Over.Hom.left (LaxPolynomialComparison.input_product_fst (Over.map b)
    (fun i => familyMap b (h i)) p q (constantFamily P X.1, constantFamily P X.2)
      (constantFamily Q Y.1, constantFamily Q Y.2) (familyMap b k.1, familyMap b k.2))

@[reassoc] theorem relativeInput_product_snd (p q : SyntaxPolynomial I) :
    (relativeInput b h X Y k (.product p q)).left ≫
        (prod.snd : object Q d Y p ⨯ object Q d Y q ⟶ object Q d Y q).left =
      (prod.snd : object P c X p ⨯ object P c X q ⟶ object P c X q).left ≫
        (relativeInput b h X Y k q).left :=
  congrArg Over.Hom.left (LaxPolynomialComparison.input_product_snd (Over.map b)
    (fun i => familyMap b (h i)) p q (constantFamily P X.1, constantFamily P X.2)
      (constantFamily Q Y.1, constantFamily Q Y.2) (familyMap b k.1, familyMap b k.2))

@[reassoc] theorem relativeInput_sum_inl (p q : SyntaxPolynomial I) :
    (coprod.inl : object P c X p ⟶ object P c X p ⨿ object P c X q).left ≫
        (relativeInput b h X Y k (.sum p q)).left =
      (relativeInput b h X Y k p).left ≫
        (coprod.inl : object Q d Y p ⟶ object Q d Y p ⨿ object Q d Y q).left :=
  congrArg Over.Hom.left (LaxPolynomialComparison.input_sum_inl (Over.map b)
    (fun i => familyMap b (h i)) p q (constantFamily P X.1, constantFamily P X.2)
      (constantFamily Q Y.1, constantFamily Q Y.2) (familyMap b k.1, familyMap b k.2))

@[reassoc] theorem relativeInput_sum_inr (p q : SyntaxPolynomial I) :
    (coprod.inr : object P c X q ⟶ object P c X p ⨿ object P c X q).left ≫
        (relativeInput b h X Y k (.sum p q)).left =
      (relativeInput b h X Y k q).left ≫
        (coprod.inr : object Q d Y q ⟶ object Q d Y p ⨿ object Q d Y q).left :=
  congrArg Over.Hom.left (LaxPolynomialComparison.input_sum_inr (Over.map b)
    (fun i => familyMap b (h i)) p q (constantFamily P X.1, constantFamily P X.2)
      (constantFamily Q Y.1, constantFamily Q Y.2) (familyMap b k.1, familyMap b k.2))

/-- The value square retains both labels and ordered recursive children.
The parameter and coefficient morphisms need not be monic. -/
theorem value_square (p : SyntaxPolynomial I) :
    (relativeInput b h X Y k p).left ≫ value Q d Y p =
      value P c X p ≫ baseInput h X Y k p := by
  induction p with
  | term => simp [relativeInput, LaxPolynomialComparison.input, LaxPolynomialComparison.component,
      value_term, baseInput, SyntaxCoefficientMorphisms.component, SyntaxPolynomial.mapCoefficients,
      SyntaxPolynomial.eval, familyMap]
  | formula => simp [relativeInput, LaxPolynomialComparison.input, LaxPolynomialComparison.component,
      value_formula, baseInput, SyntaxCoefficientMorphisms.component, SyntaxPolynomial.mapCoefficients,
      SyntaxPolynomial.eval, familyMap]
  | coefficient i => simp [relativeInput, LaxPolynomialComparison.input,
      LaxPolynomialComparison.component, value_coefficient, baseInput,
      SyntaxCoefficientMorphisms.component, SyntaxPolynomial.mapCoefficients,
      SyntaxPolynomial.eval, familyMap]
  | unit => exact terminalIsTerminal.hom_ext _ _
  | product p q hp hq =>
    apply prod.hom_ext
    · rw [Category.assoc, value_product_fst, ← Category.assoc, relativeInput_product_fst,
        Category.assoc, hp, ← Category.assoc, ← value_product_fst]
      simpa only [Category.assoc] using
        (congrArg (fun m => value P c X (.product p q) ≫ m)
          (baseInput_product_fst h X Y k p q)).symm
    · rw [Category.assoc, value_product_snd, ← Category.assoc, relativeInput_product_snd,
        Category.assoc, hq, ← Category.assoc, ← value_product_snd]
      simpa only [Category.assoc] using
        (congrArg (fun m => value P c X (.product p q) ≫ m)
          (baseInput_product_snd h X Y k p q)).symm
  | sum p q hp hq =>
    apply BinaryCofan.IsColimit.hom_ext
      (isColimitOfHasBinaryCoproductOfPreservesColimit (Over.forget P)
        (object P c X p) (object P c X q))
    · simp only [BinaryCofan.mk_inl]
      change (coprod.inl : object P c X p ⟶ object P c X p ⨿ object P c X q).left ≫
        ((relativeInput b h X Y k (.sum p q)).left ≫ value Q d Y (.sum p q)) = _
      erw [← Category.assoc, relativeInput_sum_inl, Category.assoc, value_sum_inl,
        ← Category.assoc, hp, Category.assoc]
      change value P c X p ≫ baseInput h X Y k p ≫
          (coprod.inl : (SyntaxPolynomial.mapCoefficients d p).eval.obj Y ⟶
            (p.mapCoefficients d).eval.obj Y ⨿ (q.mapCoefficients d).eval.obj Y) =
        (coprod.inl : object P c X p ⟶ object P c X p ⨿ object P c X q).left ≫
          value P c X (.sum p q) ≫ baseInput h X Y k (.sum p q)
      calc
        value P c X p ≫ baseInput h X Y k p ≫ coprod.inl =
            value P c X p ≫ coprod.inl ≫ baseInput h X Y k (.sum p q) := by
          simpa only [Category.assoc] using
            (congrArg (fun m => value P c X p ≫ m) (baseInput_sum_inl h X Y k p q)).symm
        _ = (coprod.inl : object P c X p ⟶ object P c X p ⨿ object P c X q).left ≫
            value P c X (.sum p q) ≫ baseInput h X Y k (.sum p q) := by
          simpa only [Category.assoc] using (congrArg
            (fun m => m ≫ baseInput h X Y k (.sum p q)) (value_sum_inl P c X p q)).symm
    · simp only [BinaryCofan.mk_inr]
      change (coprod.inr : object P c X q ⟶ object P c X p ⨿ object P c X q).left ≫
        ((relativeInput b h X Y k (.sum p q)).left ≫ value Q d Y (.sum p q)) = _
      erw [← Category.assoc, relativeInput_sum_inr, Category.assoc, value_sum_inr,
        ← Category.assoc, hq, Category.assoc]
      change value P c X q ≫ baseInput h X Y k q ≫
          (coprod.inr : (SyntaxPolynomial.mapCoefficients d q).eval.obj Y ⟶
            (p.mapCoefficients d).eval.obj Y ⨿ (q.mapCoefficients d).eval.obj Y) =
        (coprod.inr : object P c X q ⟶ object P c X p ⨿ object P c X q).left ≫
          value P c X (.sum p q) ≫ baseInput h X Y k (.sum p q)
      calc
        value P c X q ≫ baseInput h X Y k q ≫ coprod.inr =
            value P c X q ≫ coprod.inr ≫ baseInput h X Y k (.sum p q) := by
          simpa only [Category.assoc] using
            (congrArg (fun m => value P c X q ≫ m) (baseInput_sum_inr h X Y k p q)).symm
        _ = (coprod.inr : object P c X q ⟶ object P c X p ⨿ object P c X q).left ≫
            value P c X (.sum p q) ≫ baseInput h X Y k (.sum p q) := by
          simpa only [Category.assoc] using (congrArg
            (fun m => m ≫ baseInput h X Y k (.sum p q)) (value_sum_inr P c X p q)).symm

/-- The full slice square follows from the parameter and value projections. -/
theorem comparison_square (p : SyntaxPolynomial I) :
    relativeInput b h X Y k p ≫ comparison Q d Y p =
      (Over.map b).map (comparison P c X p) ≫ familyMap b (baseInput h X Y k p) := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w _).trans (Over.w _).symm
  · simp only [Over.comp_left, Category.assoc, familyMap_value]
    change (relativeInput b h X Y k p).left ≫
      (comparison Q d Y p).left ≫ prod.snd =
        (comparison P c X p).left ≫ prod.snd ≫ baseInput h X Y k p
    simpa only [value, Category.assoc] using value_square b h X Y k p
end CategoricalEssentialIncompleteness.V46.PolynomialParameterSquares
