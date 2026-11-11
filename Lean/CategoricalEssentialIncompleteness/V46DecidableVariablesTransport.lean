/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSyntax
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Transport of internal decidable equality through equivalences -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.DecidableVariables.Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [HasFiniteLimits C] [HasFiniteCoproducts C]
variable [HasFiniteLimits D] [HasFiniteCoproducts D]
variable (E : C ≌ D)

def terminalIso : E.functor.obj (⊤_ C) ≅ ⊤_ D :=
  asIso (terminalComparison E.functor)

def booleanIso : E.functor.obj ((⊤_ C) ⨿ (⊤_ C)) ≅ (⊤_ D) ⨿ (⊤_ D) :=
  (asIso (coprodComparison E.functor (⊤_ C) (⊤_ C))).symm ≪≫
    coprod.mapIso (terminalIso E) (terminalIso E)

def productIso (V : C) (W : D) (e : E.functor.obj V ≅ W) :
    E.functor.obj (V ⨯ V) ≅ W ⨯ W :=
  asIso (prodComparison E.functor V V) ≪≫ prod.mapIso e e

@[reassoc] theorem booleanIso_inr :
    E.functor.map (coprod.inr : ⊤_ C ⟶ (⊤_ C) ⨿ (⊤_ C)) ≫
      (booleanIso E).hom = (terminalIso E).hom ≫ coprod.inr := by
  change E.functor.map coprod.inr ≫
    (inv (coprodComparison E.functor (⊤_ C) (⊤_ C)) ≫
      coprod.map (terminalComparison E.functor) (terminalComparison E.functor)) = _
  rw [← Category.assoc, map_inr_inv_coprodComparison, coprod.inr_map]
  rfl

/-- The image test classifies the target diagonal under the actual
terminal, binary-product and Boolean coproduct comparison isomorphisms. -/
def mapped {V : C} (S : DecidableVariables V) (W : D) (e : E.functor.obj V ≅ W) :
    DecidableVariables W where
  test := (productIso E V W e).inv ≫ E.functor.map S.test ≫ (booleanIso E).hom
  diagonal := by
    apply (E.functor.map_isPullback S.diagonal).of_iso e (productIso E V W e)
      (terminalIso E) (booleanIso E)
    · apply prod.hom_ext
      · simp [productIso, Category.assoc]
        rw [← Category.assoc, ← E.functor.map_comp, prod.lift_fst,
          E.functor.map_id, Category.id_comp]
      · simp [productIso, Category.assoc]
        rw [← Category.assoc, ← E.functor.map_comp, prod.lift_snd,
          E.functor.map_id, Category.id_comp]
    · exact (Limits.terminalIsTerminal (C := D)).hom_ext _ _
    · simp only [Iso.hom_inv_id_assoc]
    · exact booleanIso_inr E

end CategoricalEssentialIncompleteness.V46.DecidableVariables.Transport
