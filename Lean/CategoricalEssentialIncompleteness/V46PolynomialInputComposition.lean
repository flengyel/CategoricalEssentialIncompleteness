/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46LaxPolynomialCoherence
public import CategoricalEssentialIncompleteness.V46PolynomialParameterValues

/-! # Composition of polynomial inputs and constant-family values -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u₁ v₁ u₂ v₂ u₃ v₃
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.PolynomialInputComposition
variable {I : Type w} {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [HasFiniteProducts A] [HasFiniteCoproducts A]
variable [HasFiniteProducts B] [HasFiniteCoproducts B]
variable [HasFiniteProducts C] [HasFiniteCoproducts C]
variable (F : A ⥤ B) (G : B ⥤ C)
variable [PreservesFiniteCoproducts F] [PreservesFiniteCoproducts G]
variable {c : I → A} {d : I → B} {e : I → C}
variable (χ : ∀ i, F.obj (c i) ⟶ d i) (ψ : ∀ i, G.obj (d i) ⟶ e i)
open LaxPolynomialComparison

theorem input_id (p : SyntaxPolynomial I) (X : A × A) :
    input F χ p X ((F.prod F).obj X) (𝟙 _) = component F χ p X := by
  dsimp only [input]
  erw [(p.mapCoefficients d).eval.map_id ((F.prod F).obj X), Category.comp_id]

theorem component_comp (p : SyntaxPolynomial I) (X : A × A) :
    component (F ⋙ G) (fun i => G.map (χ i) ≫ ψ i) p X =
      G.map (component F χ p X) ≫ component G ψ p ((F.prod F).obj X) := by
  have h := natural_square F χ (F ⋙ G) G (fun i => G.map (χ i) ≫ ψ i) ψ
    (𝟙 (F ⋙ G)) (fun _ => Category.id_comp _) p X
  simp only [NatTrans.id_app, Category.id_comp, input] at h
  change component (F ⋙ G) (fun i => G.map (χ i) ≫ ψ i) p X =
    G.map (component F χ p X) ≫ (component G ψ p ((F.prod F).obj X) ≫
      (p.mapCoefficients e).eval.map (𝟙 ((G.prod G).obj ((F.prod F).obj X)))) at h
  erw [(p.mapCoefficients e).eval.map_id ((G.prod G).obj ((F.prod F).obj X)),
    Category.comp_id] at h
  exact h

theorem input_comp (p : SyntaxPolynomial I) (X : A × A) (Y : B × B) (Z : C × C)
    (k : (F.prod F).obj X ⟶ Y) (l : (G.prod G).obj Y ⟶ Z) :
    G.map (input F χ p X Y k) ≫ input G ψ p Y Z l =
      input (F ⋙ G) (fun i => G.map (χ i) ≫ ψ i) p X Z
        ((G.prod G).map k ≫ l) := by
  dsimp only [input]
  rw [G.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (G.map ((p.mapCoefficients d).eval.map k))
      (component G ψ p Y) ((p.mapCoefficients e).eval.map l),
    LaxPolynomialComparison.naturality G ψ p k]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← Category.assoc, ← component_comp]
  rfl

end CategoricalEssentialIncompleteness.V46.PolynomialInputComposition

namespace CategoricalEssentialIncompleteness.V46.PolynomialParameterValues
variable {C : Type u₁} [Category.{v₁} C] [Regular C] [HasFiniteCoproducts C]
local instance (P : C) : Regular (Over P) := RegularSlices.regular P
variable {I : Type w}

/-- The canonical parameter comparison's value is the polynomial input of the forgetful
functor, with the value projections. -/
theorem value_as_input (P : C) (c : I → C) (X : C × C) (p : SyntaxPolynomial I) :
    value P c X p =
      LaxPolynomialComparison.input (Over.forget P) (fun i => (prod.snd : P ⨯ c i ⟶ c i)) p
        (constantFamily P X.1, constantFamily P X.2) X (prod.snd, prod.snd) := by
  induction p with
  | term =>
    rw [value_term]
    change prod.snd = 𝟙 _ ≫ prod.snd
    exact (Category.id_comp _).symm
  | formula =>
    rw [value_formula]
    change prod.snd = 𝟙 _ ≫ prod.snd
    exact (Category.id_comp _).symm
  | coefficient i => simp [value, comparison, LaxPolynomialComparison.input,
      LaxPolynomialComparison.component, SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval]
  | unit =>
    change (constantUnitComparison P).left ≫ prod.snd = _
    change (prod.lift _ _ ≫ prod.snd) = _
    rw [prod.lift_snd]
    exact terminalIsTerminal.hom_ext _ _
  | product p q hp hq =>
    apply prod.hom_ext
    · rw [value_product_fst, LaxPolynomialComparison.input_product_fst, hp]
      rfl
    · rw [value_product_snd, LaxPolynomialComparison.input_product_snd, hq]
      rfl
  | sum p q hp hq =>
    apply (cancel_epi (coprodComparison (Over.forget P) (object P c X p)
      (object P c X q))).mp
    apply coprod.hom_ext
    · simp only [← Category.assoc, coprodComparison, coprod.inl_desc]
      erw [value_sum_inl, LaxPolynomialComparison.input_sum_inl]
      rw [hp]
    · simp only [← Category.assoc, coprodComparison, coprod.inr_desc]
      erw [value_sum_inr, LaxPolynomialComparison.input_sum_inr]
      rw [hq]

end CategoricalEssentialIncompleteness.V46.PolynomialParameterValues
