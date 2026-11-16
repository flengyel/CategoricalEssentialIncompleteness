/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkFirstOrderFormula
public import CategoricalEssentialIncompleteness.V46DiagramPolynomialComparison
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Decidable equality on constant variable diagrams -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂ v₃ u₃
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.DiagramDecidableVariables
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [HasFiniteLimits C] [HasFiniteCoproducts C]
variable [HasFiniteLimits D] [HasFiniteCoproducts D]
variable (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteCoproducts F]

def terminalIso : F.obj (⊤_ C) ≅ ⊤_ D :=
  asIso (terminalComparison F)

def booleanIso : F.obj ((⊤_ C) ⨿ (⊤_ C)) ≅ (⊤_ D) ⨿ (⊤_ D) :=
  (asIso (coprodComparison F (⊤_ C) (⊤_ C))).symm ≪≫
    coprod.mapIso (terminalIso F) (terminalIso F)

def productIso (V : C) (W : D) (e : F.obj V ≅ W) :
    F.obj (V ⨯ V) ≅ W ⨯ W :=
  asIso (prodComparison F V V) ≪≫ prod.mapIso e e

@[reassoc] theorem booleanIso_inr :
    F.map (coprod.inr : ⊤_ C ⟶ (⊤_ C) ⨿ (⊤_ C)) ≫
      (booleanIso F).hom = (terminalIso F).hom ≫ coprod.inr := by
  change F.map coprod.inr ≫
    (inv (coprodComparison F (⊤_ C) (⊤_ C)) ≫
      coprod.map (terminalComparison F) (terminalComparison F)) = _
  rw [← Category.assoc, map_inr_inv_coprodComparison, coprod.inr_map]
  rfl

/-- The image test classifies the target diagonal under the actual
terminal, binary-product and Boolean coproduct comparison isomorphisms. -/
def mapped {V : C} (S : DecidableVariables V) (W : D) (e : F.obj V ≅ W) :
    DecidableVariables W where
  test := (productIso F V W e).inv ≫ F.map S.test ≫ (booleanIso F).hom
  diagonal := by
    apply (F.map_isPullback S.diagonal).of_iso e (productIso F V W e)
      (terminalIso F) (booleanIso F)
    · apply prod.hom_ext
      · simp [productIso, Category.assoc]
        rw [← Category.assoc, ← F.map_comp, prod.lift_fst,
          F.map_id, Category.id_comp]
      · simp [productIso, Category.assoc]
        rw [← Category.assoc, ← F.map_comp, prod.lift_snd,
          F.map_id, Category.id_comp]
    · exact (Limits.terminalIsTerminal (C := D)).hom_ext _ _
    · simp only [Iso.hom_inv_id_assoc]
    · exact booleanIso_inr F

/-- A constant diagram retains the internal variable equality test under
its actual terminal, product and Boolean comparison isomorphisms. -/
def constant {J : Type u₃} [Category.{v₃} J] {V : C} (S : DecidableVariables V) :
    DecidableVariables ((Functor.const J).obj V) :=
  mapped (Functor.const J) S _ (Iso.refl _)

/-- This is the variable diagram specified in Proposition 10.7. -/
def fork : DecidableVariables ForkFirstOrderFormula.numbers :=
  constant (ConcreteDecidableVariables.numerical _)

/-- Truth is the second Boolean injection, as in the printed convention. -/
theorem fork_diagonal :
    IsPullback (prod.lift (𝟙 ForkFirstOrderFormula.numbers) (𝟙 _))
      (terminal.from _) fork.test coprod.inr := fork.diagonal

end CategoricalEssentialIncompleteness.V46.DiagramDecidableVariables
