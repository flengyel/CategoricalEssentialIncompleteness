/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46NumericalDiagramSyntax
public import CategoricalEssentialIncompleteness.V46LaxPolynomialComparison
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

/-! # Canonical polynomial evaluation in a functor category -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u₁ v₁ u₂ v₂ w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.DiagramPolynomialComparison
variable {J : Type u₁} [Category.{v₁} J] {C : Type u₂} [Category.{v₂} C]
variable [HasFiniteProducts C] [HasFiniteCoproducts C] {I : Type w}
instance evaluation_preservesFiniteProducts (j : J) :
    PreservesFiniteProducts ((evaluation J C).obj j) where
  preserves _ := inferInstance
instance evaluation_preservesFiniteCoproducts (j : J) :
    PreservesFiniteCoproducts ((evaluation J C).obj j) where
  preserves _ := inferInstance
variable (c : I → J ⥤ C) (X : (J ⥤ C) × (J ⥤ C))

abbrev localCoefficients (j : J) (i : I) : C := (c i).obj j
abbrev localCarrier (j : J) : C × C := (X.1.obj j, X.2.obj j)

/-- Forward evaluation comparison, using the chosen products and coproducts
in the functor category and in its value category. -/
def component (p : SyntaxPolynomial I) (j : J) :
    ((p.mapCoefficients c).eval.obj X).obj j ⟶
      (p.mapCoefficients (localCoefficients c j)).eval.obj (localCarrier X j) :=
  LaxPolynomialComparison.component ((evaluation J C).obj j) (fun _ => 𝟙 _) p X

instance component_isIso (p : SyntaxPolynomial I) (j : J) :
    IsIso (component c X p j) := by
  induction p with
  | term => change IsIso (𝟙 _); infer_instance
  | formula => change IsIso (𝟙 _); infer_instance
  | coefficient => change IsIso (𝟙 _); infer_instance
  | unit => change IsIso (terminalComparison ((evaluation J C).obj j)); infer_instance
  | product p q hp hq =>
    change IsIso (prodComparison ((evaluation J C).obj j) _ _ ≫
      prod.map (component c X p j) (component c X q j))
    infer_instance
  | sum p q hp hq =>
    change IsIso (inv (coprodComparison ((evaluation J C).obj j) _ _) ≫
      coprod.map (component c X p j) (component c X q j))
    infer_instance

/-- The literal polynomial action along a diagram morphism retains every
coefficient transition and both recursive carrier transitions. -/
def transition (p : SyntaxPolynomial I) {j k : J} (f : j ⟶ k) :
    (p.mapCoefficients (localCoefficients c j)).eval.obj (localCarrier X j) ⟶
      (p.mapCoefficients (localCoefficients c k)).eval.obj (localCarrier X k) :=
  match p with
  | .term => X.1.map f
  | .formula => X.2.map f
  | .coefficient i => (c i).map f
  | .unit => 𝟙 _
  | .product p q => prod.map (transition p f) (transition q f)
  | .sum p q => coprod.map (transition p f) (transition q f)

@[reassoc] theorem component_product_fst (p q : SyntaxPolynomial I) (j : J) :
    component c X (.product p q) j ≫ prod.fst =
      (prod.fst : (p.mapCoefficients c).eval.obj X ⨯
        (q.mapCoefficients c).eval.obj X ⟶ _).app j ≫ component c X p j := by
  dsimp only [component, LaxPolynomialComparison.component,
    SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor]
  erw [Category.assoc, prod.map_fst, ← Category.assoc, prodComparison_fst]
  rfl

@[reassoc] theorem component_product_snd (p q : SyntaxPolynomial I) (j : J) :
    component c X (.product p q) j ≫ prod.snd =
      (prod.snd : (p.mapCoefficients c).eval.obj X ⨯
        (q.mapCoefficients c).eval.obj X ⟶ _).app j ≫ component c X q j := by
  dsimp only [component, LaxPolynomialComparison.component,
    SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor]
  erw [Category.assoc, prod.map_snd, ← Category.assoc, prodComparison_snd]
  rfl

@[reassoc] theorem component_sum_inl (p q : SyntaxPolynomial I) (j : J) :
    (coprod.inl : (p.mapCoefficients c).eval.obj X ⟶
        (p.mapCoefficients c).eval.obj X ⨿ (q.mapCoefficients c).eval.obj X).app j ≫
      component c X (.sum p q) j = component c X p j ≫ coprod.inl := by
  dsimp only [component, LaxPolynomialComparison.component,
    SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor]
  erw [← Category.assoc,
    map_inl_inv_coprodComparison ((evaluation J C).obj j)
      (A := (p.mapCoefficients c).eval.obj X) (B := (q.mapCoefficients c).eval.obj X),
    coprod.inl_map]
  rfl

@[reassoc] theorem component_sum_inr (p q : SyntaxPolynomial I) (j : J) :
    (coprod.inr : (q.mapCoefficients c).eval.obj X ⟶
        (p.mapCoefficients c).eval.obj X ⨿ (q.mapCoefficients c).eval.obj X).app j ≫
      component c X (.sum p q) j = component c X q j ≫ coprod.inr := by
  dsimp only [component, LaxPolynomialComparison.component,
    SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor]
  erw [← Category.assoc,
    map_inr_inv_coprodComparison ((evaluation J C).obj j)
      (A := (p.mapCoefficients c).eval.obj X) (B := (q.mapCoefficients c).eval.obj X),
    coprod.inr_map]
  rfl

/-- Polynomial evaluation is natural in the diagram index, including
coefficient morphisms that identify labels. -/
theorem component_transition (p : SyntaxPolynomial I) {j k : J} (f : j ⟶ k) :
    ((p.mapCoefficients c).eval.obj X).map f ≫ component c X p k =
      component c X p j ≫ transition c X p f := by
  induction p with
  | term => change X.1.map f ≫ 𝟙 _ = 𝟙 _ ≫ X.1.map f; simp
  | formula => change X.2.map f ≫ 𝟙 _ = 𝟙 _ ≫ X.2.map f; simp
  | coefficient i => change (c i).map f ≫ 𝟙 _ = 𝟙 _ ≫ (c i).map f; simp
  | unit =>
    change _ ≫ terminalComparison ((evaluation J C).obj k) =
      terminalComparison ((evaluation J C).obj j) ≫ 𝟙 _
    exact terminalIsTerminal.hom_ext _ _
  | product p q hp hq =>
    dsimp only [SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval,
      SyntaxPolynomial.productFunctor]
    apply prod.hom_ext
    · simp only [Category.assoc, component_product_fst, transition,
        prod.map_fst, component_product_fst_assoc]
      rw [← Category.assoc, (prod.fst : (p.mapCoefficients c).eval.obj X ⨯
        (q.mapCoefficients c).eval.obj X ⟶ _).naturality f, Category.assoc, hp]
    · simp only [Category.assoc, component_product_snd, transition,
        prod.map_snd, component_product_snd_assoc]
      rw [← Category.assoc, (prod.snd : (p.mapCoefficients c).eval.obj X ⨯
        (q.mapCoefficients c).eval.obj X ⟶ _).naturality f, Category.assoc, hq]
  | sum p q hp hq =>
    dsimp only [SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval,
      SyntaxPolynomial.sumFunctor]
    apply (cancel_epi (coprodComparison ((evaluation J C).obj j)
      ((p.mapCoefficients c).eval.obj X) ((q.mapCoefficients c).eval.obj X))).mp
    apply coprod.hom_ext
    · simp only [← Category.assoc, coprodComparison, coprod.inl_desc]
      erw [← (coprod.inl : (p.mapCoefficients c).eval.obj X ⟶
        (p.mapCoefficients c).eval.obj X ⨿ (q.mapCoefficients c).eval.obj X).naturality f]
      erw [Category.assoc, component_sum_inl c X p q k, component_sum_inl c X p q j]
      simp only [Category.assoc, transition, coprod.inl_map]
      simpa only [Category.assoc] using congrArg (fun n => n ≫ coprod.inl) hp
    · simp only [← Category.assoc, coprodComparison, coprod.inr_desc]
      erw [← (coprod.inr : (q.mapCoefficients c).eval.obj X ⟶
        (p.mapCoefficients c).eval.obj X ⨿ (q.mapCoefficients c).eval.obj X).naturality f]
      erw [Category.assoc, component_sum_inr c X p q k, component_sum_inr c X p q j]
      simp only [Category.assoc, transition, coprod.inr_map]
      simpa only [Category.assoc] using congrArg (fun n => n ≫ coprod.inr) hq

/-- The transition agrees with coefficient action and recursive evaluation. -/
theorem transition_eq (p : SyntaxPolynomial I) {j k : J} (f : j ⟶ k) :
    transition c X p f =
      (p.mapCoefficients (localCoefficients c j)).eval.map (X.1.map f, X.2.map f) ≫
        SyntaxCoefficientMorphisms.component (fun i => (c i).map f) p (localCarrier X k) := by
  induction p with
  | term => simp [transition, SyntaxCoefficientMorphisms.component,
      SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval]
  | formula => simp [transition, SyntaxCoefficientMorphisms.component,
      SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval]
  | coefficient => simp [transition, SyntaxCoefficientMorphisms.component,
      SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval]
  | unit => simp [transition, SyntaxCoefficientMorphisms.component,
      SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval]
  | product p q hp hq =>
    simpa only [transition, SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval,
      SyntaxPolynomial.productFunctor, SyntaxCoefficientMorphisms.component,
      prod.map_map] using congrArg₂ prod.map hp hq
  | sum p q hp hq =>
    simpa only [transition, SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval,
      SyntaxPolynomial.sumFunctor, SyntaxCoefficientMorphisms.component,
      coprod.map_map] using congrArg₂ coprod.map hp hq

end CategoricalEssentialIncompleteness.V46.DiagramPolynomialComparison

namespace CategoricalEssentialIncompleteness.V46.SyntaxPolynomial

@[simp] theorem mapCoefficients_id {I : Type w} (p : SyntaxPolynomial I) :
    p.mapCoefficients id = p := by
  induction p with
  | term => rfl
  | formula => rfl
  | coefficient => rfl
  | unit => rfl
  | product p q hp hq => simp only [mapCoefficients, hp, hq]
  | sum p q hp hq => simp only [mapCoefficients, hp, hq]

end CategoricalEssentialIncompleteness.V46.SyntaxPolynomial
