/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialMapFunctor
public import Mathlib.CategoryTheory.EqToHom

/-! # Identity and composition of functors on monic partial maps -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.PartialMaps

variable {D : Type u₁} [Category.{v₁} D] [HasPullbacks D]
variable {E : Type u₂} [Category.{v₂} E] [HasPullbacks E]
variable {H : Type u₃} [Category.{v₃} H] [HasPullbacks H]

theorem inducedFunctor_id : inducedFunctor (𝟭 D) = 𝟭 (Par D) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  induction f using Quotient.inductionOn with | _ s => rfl

theorem inducedFunctor_congr (F₁ F₂ : D ⥤ E)
    [F₁.PreservesMonomorphisms] [F₂.PreservesMonomorphisms]
    [PreservesLimitsOfShape WalkingCospan F₁] [PreservesLimitsOfShape WalkingCospan F₂]
    (h : F₁ = F₂) : inducedFunctor F₁ = inducedFunctor F₂ := by
  cases h
  rfl

variable (F : D ⥤ E) (G : E ⥤ H) [F.PreservesMonomorphisms] [G.PreservesMonomorphisms]
variable [PreservesLimitsOfShape WalkingCospan F] [PreservesLimitsOfShape WalkingCospan G]

theorem inducedFunctor_comp : inducedFunctor (F ⋙ G) = inducedFunctor F ⋙ inducedFunctor G := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  induction f using Quotient.inductionOn with | _ s => rfl

end CategoricalEssentialIncompleteness.V46.PartialMaps
