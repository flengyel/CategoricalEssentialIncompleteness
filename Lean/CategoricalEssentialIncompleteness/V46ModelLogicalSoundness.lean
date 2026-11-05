/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46LogicalSchemes

/-! # Semantic propositional schemes with an opaque model functor -/

noncomputable section
universe v u w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ModelLogicalSoundness
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable (G : C ⥤ Type w) {Fm : C}

theorem map_lift_fst {Z A B : C} (f : Z ⟶ A) (g : Z ⟶ B) (z : G.obj Z) :
    G.map (prod.fst : A ⨯ B ⟶ A) (G.map (prod.lift f g) z) = G.map f z := by
  rw [← Functor.map_comp_apply,prod.lift_fst]

theorem map_lift_snd {Z A B : C} (f : Z ⟶ A) (g : Z ⟶ B) (z : G.obj Z) :
    G.map (prod.snd : A ⨯ B ⟶ B) (G.map (prod.lift f g) z) = G.map g z := by
  rw [← Functor.map_comp_apply,prod.lift_snd]

variable (imp : Fm ⨯ Fm ⟶ Fm) (P : G.obj Fm → Prop)
variable (himp : ∀ z : G.obj (Fm ⨯ Fm), P (G.map imp z) ↔
  (P (G.map (prod.fst : Fm ⨯ Fm ⟶ Fm) z) → P (G.map (prod.snd : Fm ⨯ Fm ⟶ Fm) z)))

include himp

theorem valid_one (z : G.obj (Fm ⨯ Fm)) :
    P (G.map (prod.lift prod.fst (prod.lift prod.snd prod.fst ≫ imp) ≫ imp) z) := by
  simp only [Functor.map_comp_apply,himp,map_lift_fst,map_lift_snd]
  exact fun hφ _ => hφ

theorem valid_two (z : G.obj ((Fm ⨯ Fm) ⨯ Fm)) :
    P (G.map (prod.lift
      (prod.lift (prod.fst ≫ prod.fst)
        (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ imp) ≫ imp)
      (prod.lift (prod.fst ≫ imp)
        (prod.lift (prod.fst ≫ prod.fst) prod.snd ≫ imp) ≫ imp) ≫ imp) z) := by
  simp only [Functor.map_comp_apply,himp,map_lift_fst,map_lift_snd]
  exact fun h₁ h₂ hφ => h₁ hφ (h₂ hφ)

theorem valid_three (neg : Fm ⟶ Fm)
    (hneg : ∀ φ : G.obj Fm, P (G.map neg φ) ↔ ¬ P φ) (z : G.obj (Fm ⨯ Fm)) :
    P (G.map (prod.lift
      (prod.lift (prod.snd ≫ neg) (prod.fst ≫ neg) ≫ imp) imp ≫ imp) z) := by
  simp only [Functor.map_comp_apply,himp,hneg,map_lift_fst,map_lift_snd]
  intro h hφ
  classical
  by_contra hψ
  exact h hψ hφ

end CategoricalEssentialIncompleteness.V46.ModelLogicalSoundness
