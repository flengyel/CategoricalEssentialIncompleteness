/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialSlicePostcompose

/-! # Proper parameter inclusions fail essential surjectivity -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialSliceProperness

open RestrictionSubobjects AmbientPartialSlice
variable {C : Type u} [Category.{v} C] [RestrictionCategory C]
variable {T U : Tot C} (i : T ⟶ U) [Mono i]

theorem isIso_of_terminal_image (X : Family T.obj)
    (j : PartialSlicePostcompose.object i X ≅ terminalFamily U.obj) : IsIso i := by
  let a : X.base ⟶ U.obj := j.hom.hom
  let b : U.obj ⟶ X.base := j.inv.hom
  have hj : isTotal a := (AmbientPartialSlice.total_iff j.hom).mp (iso_total j)
  have h : a = X.proj ≫ i.hom := by
    have h := j.hom.over
    change a ≫ 𝟙 U.obj = rst a ≫ (X.proj ≫ i.hom) at h
    rwa [Category.comp_id, hj, Category.id_comp] at h
  have hba : b ≫ a = 𝟙 U.obj :=
    congrArg (fun k : terminalFamily U.obj ⟶ terminalFamily U.obj => k.hom) j.inv_hom_id
  let s : U ⟶ T :=
    ⟨b ≫ X.proj,
      isTotal_comp ((AmbientPartialSlice.total_iff j.inv).mp (iso_total j.symm)) X.total⟩
  have hs : s ≫ i = 𝟙 U := by
    apply WideSubcategory.hom_ext
    change (b ≫ X.proj) ≫ i.hom = 𝟙 U.obj
    rw [Category.assoc, ← h]
    exact hba
  have hi : i ≫ s = 𝟙 T := by
    apply (cancel_mono i).mp
    rw [Category.assoc, hs, Category.comp_id, Category.id_comp]
  exact ⟨⟨s, hi, hs⟩⟩

theorem not_essSurj (proper : ¬ IsIso i) : ¬ (PartialSlicePostcompose.functor i).EssSurj := by
  intro h
  let : (PartialSlicePostcompose.functor i).EssSurj := h
  exact proper (isIso_of_terminal_image i
    ((PartialSlicePostcompose.functor i).objPreimage (terminalFamily U.obj))
    ((PartialSlicePostcompose.functor i).objObjPreimageIso (terminalFamily U.obj)))

end CategoricalEssentialIncompleteness.V46.PartialSliceProperness
