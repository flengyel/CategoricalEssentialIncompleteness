/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46LaxPolynomialInputs

/-! # Coherence of forward polynomial comparisons -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u₁ v₁ u₂ v₂ u₃ v₃
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.LaxPolynomialComparison
variable {I : Type w} {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [HasFiniteProducts A] [HasFiniteCoproducts A]
variable [HasFiniteProducts B] [HasFiniteCoproducts B]
variable [HasFiniteProducts C] [HasFiniteCoproducts C]
variable (F : A ⥤ B) [PreservesFiniteCoproducts F]
variable {c : I → A} {d : I → B} (χ : ∀ i, F.obj (c i) ⟶ d i)

@[reassoc] theorem component_product_fst (p q : SyntaxPolynomial I) (X : A × A) :
    component F χ (.product p q) X ≫ prod.fst =
      F.map prod.fst ≫ component F χ p X := by
  dsimp only [component, SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval,
    SyntaxPolynomial.productFunctor]
  simp only [Category.assoc, prod.map_fst,
    prodComparison_fst_assoc]

@[reassoc] theorem component_product_snd (p q : SyntaxPolynomial I) (X : A × A) :
    component F χ (.product p q) X ≫ prod.snd =
      F.map prod.snd ≫ component F χ q X := by
  dsimp only [component, SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval,
    SyntaxPolynomial.productFunctor]
  simp only [Category.assoc, prod.map_snd,
    prodComparison_snd_assoc]

@[reassoc] theorem component_sum_inl (p q : SyntaxPolynomial I) (X : A × A) :
    F.map coprod.inl ≫ component F χ (.sum p q) X =
      component F χ p X ≫ coprod.inl := by
  dsimp only [component, SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval,
    SyntaxPolynomial.sumFunctor]
  rw [← Category.assoc, map_inl_inv_coprodComparison, coprod.inl_map]

@[reassoc] theorem component_sum_inr (p q : SyntaxPolynomial I) (X : A × A) :
    F.map coprod.inr ≫ component F χ (.sum p q) X =
      component F χ q X ≫ coprod.inr := by
  dsimp only [component, SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval,
    SyntaxPolynomial.sumFunctor]
  rw [← Category.assoc, map_inr_inv_coprodComparison, coprod.inr_map]

/-- When products and coefficients are preserved, the forward comparison
is an isomorphism. This is not imposed on changes of parameter. -/
instance component_isIso [PreservesFiniteProducts F] [∀ i, IsIso (χ i)]
    (p : SyntaxPolynomial I) (X : A × A) : IsIso (component F χ p X) := by
  induction p with
  | term => change IsIso (𝟙 _); infer_instance
  | formula => change IsIso (𝟙 _); infer_instance
  | coefficient i => change IsIso (χ i); infer_instance
  | unit => change IsIso (terminalComparison F); infer_instance
  | product p q hp hq =>
    change IsIso (prodComparison F _ _ ≫ prod.map (component F χ p X) (component F χ q X))
    infer_instance
  | sum p q hp hq =>
    change IsIso (inv (coprodComparison F _ _) ≫ coprod.map (component F χ p X) (component F χ q X))
    infer_instance

variable (G : A ⥤ C) (H : B ⥤ C)
variable [PreservesFiniteCoproducts G] [PreservesFiniteCoproducts H]
variable {e : I → C} (ψ : ∀ i, G.obj (c i) ⟶ e i) (δ : ∀ i, H.obj (d i) ⟶ e i)
variable (η : F ⋙ H ⟶ G)

/-- Coherence needs only forward product comparisons. The natural
transformation and every coefficient morphism may identify labels. -/
theorem natural_square (hc : ∀ i, η.app (c i) ≫ ψ i = H.map (χ i) ≫ δ i)
    (p : SyntaxPolynomial I) (X : A × A) :
    η.app ((p.mapCoefficients c).eval.obj X) ≫ component G ψ p X =
      H.map (component F χ p X) ≫
        input H δ p ((F.prod F).obj X) ((G.prod G).obj X)
          (η.app X.1, η.app X.2) := by
  induction p with
  | term =>
    change η.app X.1 ≫ 𝟙 _ = H.map (𝟙 _) ≫ (𝟙 _ ≫ η.app X.1)
    simp
  | formula =>
    change η.app X.2 ≫ 𝟙 _ = H.map (𝟙 _) ≫ (𝟙 _ ≫ η.app X.2)
    simp
  | coefficient i =>
    change η.app (c i) ≫ ψ i = H.map (χ i) ≫ (δ i ≫ 𝟙 _)
    simpa using hc i
  | unit => exact terminalIsTerminal.hom_ext _ _
  | product p q hp hq =>
    apply prod.hom_ext
    · simp only [Category.assoc]
      erw [component_product_fst G ψ p q X,
        input_product_fst H δ p q ((F.prod F).obj X) ((G.prod G).obj X)
          (η.app X.1, η.app X.2)]
      erw [← Category.assoc, ← η.naturality, Category.assoc, hp]
      dsimp only [Functor.comp_map]
      rw [← H.map_comp_assoc, ← component_product_fst F χ p q X,
        H.map_comp, Category.assoc]
      rfl
    · simp only [Category.assoc]
      erw [component_product_snd G ψ p q X,
        input_product_snd H δ p q ((F.prod F).obj X) ((G.prod G).obj X)
          (η.app X.1, η.app X.2)]
      erw [← Category.assoc, ← η.naturality, Category.assoc, hq]
      dsimp only [Functor.comp_map]
      rw [← H.map_comp_assoc, ← component_product_snd F χ p q X,
        H.map_comp, Category.assoc]
      rfl
  | sum p q hp hq =>
    apply (cancel_epi (coprodComparison (F ⋙ H)
      ((p.mapCoefficients c).eval.obj X) ((q.mapCoefficients c).eval.obj X))).mp
    apply coprod.hom_ext
    · simp only [← Category.assoc, coprodComparison, coprod.inl_desc]
      erw [η.naturality (coprod.inl : (p.mapCoefficients c).eval.obj X ⟶
        (p.mapCoefficients c).eval.obj X ⨿ (q.mapCoefficients c).eval.obj X)]
      erw [Category.assoc, component_sum_inl G ψ p q X]
      rw [← Category.assoc, hp]
      dsimp only [Functor.comp_map]
      erw [← H.map_comp, component_sum_inl F χ p q X, H.map_comp, Category.assoc]
      simp only [Category.assoc]
      erw [input_sum_inl H δ p q ((F.prod F).obj X) ((G.prod G).obj X)
        (η.app X.1, η.app X.2)]
      rfl
    · simp only [← Category.assoc, coprodComparison, coprod.inr_desc]
      erw [η.naturality (coprod.inr : (q.mapCoefficients c).eval.obj X ⟶
        (p.mapCoefficients c).eval.obj X ⨿ (q.mapCoefficients c).eval.obj X)]
      erw [Category.assoc, component_sum_inr G ψ p q X]
      rw [← Category.assoc, hq]
      dsimp only [Functor.comp_map]
      erw [← H.map_comp, component_sum_inr F χ p q X, H.map_comp, Category.assoc]
      simp only [Category.assoc]
      erw [input_sum_inr H δ p q ((F.prod F).obj X) ((G.prod G).obj X)
        (η.app X.1, η.app X.2)]
      rfl

end CategoricalEssentialIncompleteness.V46.LaxPolynomialComparison
