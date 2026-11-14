/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RegularImage
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Extensive

/-! # Regularity and finite extensivity of ordinary total slices -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.RegularSlices

variable {C : Type u} [Category.{v} C] [Regular C] (P : C)

theorem underlying_regularEpi {X Y : Over P} (f : X ⟶ Y) [IsRegularEpi f] :
    IsRegularEpi f.left := by
  let r := IsRegularEpi.getStruct f
  exact isRegularEpi_of_regularEpi {
    W := r.W.left
    left := r.left.left
    right := r.right.left
    w := congrArg Over.Hom.left r.w
    isColimit := (isColimitMapCoconeCoforkEquiv (Over.forget P) r.w)
      (isColimitOfPreserves (Over.forget P) r.isColimit) }

theorem regularEpi_of_underlying {X Y : Over P} (f : X ⟶ Y) [IsRegularEpi f.left] :
    IsRegularEpi f := by
  let : IsRegularEpi ((Over.forget P).map f) := by
    change IsRegularEpi f.left
    infer_instance
  let k := IsKernelPair.of_hasPullback f
  have hk := k.map (Over.forget P)
  have hcol : IsColimit (Cofork.ofπ f k.w) := by
    apply isColimitOfReflects (Over.forget P)
    exact (isColimitMapCoconeCoforkEquiv (Over.forget P) k.w).symm
      (IsKernelPair.toCoequalizer' hk)
  exact isRegularEpi_of_regularEpi (regularEpiOfKernelPair f hcol)

theorem regular : Regular (Over P) where
  toHasFiniteLimits := inferInstance
  hasCoequalizer_of_isKernelPair {X Y Z} {f} {g₁ g₂} h := by
    let : HasCoequalizer g₁.left g₂.left :=
      Regular.hasCoequalizer_of_isKernelPair (h.map (Over.forget P))
    let e : parallelPair g₁ g₂ ⋙ Over.forget P ≅ parallelPair g₁.left g₂.left :=
      NatIso.ofComponents (fun j => by cases j <;> exact Iso.refl _)
        (by intro i j f; cases f <;> simp)
    let : HasColimit (parallelPair g₁ g₂ ⋙ Over.forget P) := hasColimit_of_iso e
    exact Over.hasColimit_of_hasColimit_comp_forget (parallelPair g₁ g₂)
  regularEpiIsStableUnderBaseChange := by
    apply MorphismProperty.IsStableUnderBaseChange.of_forall_exists_isPullback
    intro X Y Z f g _ hg
    let : IsRegularEpi g := hg
    let : IsRegularEpi g.left := underlying_regularEpi P g
    have hp := (IsPullback.of_hasPullback g f).map (Over.forget P)
    have hp' : IsPullback (pullback.fst g f).left (pullback.snd g f).left g.left f.left := hp
    have hreg : IsRegularEpi (pullback.snd g f).left := by
      apply Regular.regularEpiIsStableUnderBaseChange.of_isPullback hp'
      change IsRegularEpi g.left
      infer_instance
    let := hreg
    exact ⟨pullback g f, pullback.snd g f, pullback.fst g f,
      (IsPullback.of_hasPullback g f).flip, regularEpi_of_underlying P _⟩

theorem finitaryExtensive [FinitaryExtensive C] : FinitaryExtensive (Over P) :=
  finitaryExtensive_of_preserves_and_reflects (Over.forget P)

end CategoricalEssentialIncompleteness.V46.RegularSlices
