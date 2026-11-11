/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Mathlib.CategoryTheory.RegularCategory.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.EffectiveEpi.Preserves
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Regular categories under an equivalence -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.RegularEquivalence
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [HasFiniteLimits C] [HasFiniteLimits D] (E : C ≌ D)

theorem regularEpi_iff {X Y : C} (f : X ⟶ Y) :
    IsRegularEpi (E.functor.map f) ↔ IsRegularEpi f := by
  rw [isRegularEpi_iff_effectiveEpi, isRegularEpi_iff_effectiveEpi]
  constructor
  · exact E.functor.effectiveEpi_of_map f
  · intro h
    let : EffectiveEpi f := h
    infer_instance

omit [HasFiniteLimits C]
include E

/-- Kernel-pair coequalizers and pullback stability transport through
the functor and inverse, without any splitting hypothesis on epimorphisms. -/
theorem regular [Regular C] : Regular D where
  hasCoequalizer_of_isKernelPair {X Y Z f g₁ g₂} k := by
    let : HasCoequalizer (E.inverse.map g₁) (E.inverse.map g₂) :=
      Regular.hasCoequalizer_of_isKernelPair (E.inverse.map_isPullback k)
    let : HasColimit (parallelPair
        ((parallelPair g₁ g₂ ⋙ E.inverse).map WalkingParallelPairHom.left)
        ((parallelPair g₁ g₂ ⋙ E.inverse).map WalkingParallelPairHom.right)) := by
      change HasCoequalizer (E.inverse.map g₁) (E.inverse.map g₂)
      infer_instance
    let : HasColimit (parallelPair g₁ g₂ ⋙ E.inverse) :=
      hasColimit_of_iso (diagramIsoParallelPair (parallelPair g₁ g₂ ⋙ E.inverse))
    exact Adjunction.hasColimit_of_comp_equivalence (parallelPair g₁ g₂) E.inverse
  regularEpiIsStableUnderBaseChange :=
    { of_isPullback := by
        intro X Y Y' S f g f' g' sq hg
        have hm : IsRegularEpi (E.inverse.map g) :=
          (regularEpi_iff E.symm g).mpr hg
        have hn : IsRegularEpi (E.inverse.map g') :=
          Regular.regularEpiIsStableUnderBaseChange.of_isPullback
            (E.inverse.map_isPullback sq) hm
        exact (regularEpi_iff E.symm g').mp hn }

end CategoricalEssentialIncompleteness.V46.RegularEquivalence
