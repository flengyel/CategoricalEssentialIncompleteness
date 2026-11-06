/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntaxOptionTransport
import CategoricalEssentialIncompleteness.V46CategoricalQuantifierAdmissibilityOptions

/-! # The genuine Boolean classifier of an option's success pullback -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxOptionTransport
variable {C : Type u} [Category.{v} C] [Regular C] [FinitaryExtensive C]

/-- This arrow classifies success of an option. It does not define any
independently specified numerical admissibility or free-for algorithm. -/
def optionTag (Y : C) : OptionSyntax.obj Y ⟶ Two C :=
  OptionSyntax.map (terminal.from Y)

@[reassoc] theorem optionTag_inl (Y : C) :
    (coprod.inl : ⊤_ C ⟶ OptionSyntax.obj Y) ≫ optionTag Y = Two.point false := by
  simp only [optionTag,OptionSyntax.map,coprod.inl_map,Two.point,Category.id_comp]

@[reassoc] theorem optionTag_inr (Y : C) :
    (coprod.inr : Y ⟶ OptionSyntax.obj Y) ≫ optionTag Y =
      terminal.from Y ≫ Two.point true := by
  simp only [optionTag,OptionSyntax.map,coprod.inr_map,Two.point]

/-- The success injection itself is the actual pullback of true,
including when Y is empty. -/
theorem optionTag_isPullback (Y : C) :
    IsPullback (coprod.inr : Y ⟶ OptionSyntax.obj Y) (terminal.from Y)
      (optionTag Y) (Two.point (C := C) true) := by
  have hv := (BinaryCofan.isVanKampen_iff _).mp
    (FinitaryExtensive.vanKampen _ (coprodIsCoprod (⊤_ C) (⊤_ C)))
    (BinaryCofan.mk (coprod.inl : ⊤_ C ⟶ OptionSyntax.obj Y) coprod.inr)
  exact ((hv (𝟙 _) (terminal.from Y) (optionTag Y)
    (by simp [optionTag,OptionSyntax.map]) (by simp [optionTag,OptionSyntax.map])).mp
      ⟨coprodIsCoprod (⊤_ C) Y⟩).2

/-- Pasting the actual success pullback with its classifier gives a
pullback of true on the original input object. -/
theorem optionTag_success_isPullback {X Y : C} (f : X ⟶ OptionSyntax.obj Y) :
    IsPullback (pullback.fst f (coprod.inr : Y ⟶ OptionSyntax.obj Y))
      (terminal.from (pullback f (coprod.inr : Y ⟶ OptionSyntax.obj Y)))
      (f ≫ optionTag Y) (Two.point (C := C) true) := by
  have h := (IsPullback.of_hasPullback f (coprod.inr : Y ⟶ OptionSyntax.obj Y)).paste_vert
    (optionTag_isPullback Y)
  simpa only [terminal.comp_from] using h

theorem optionTag_success_subobject {X Y : C} (f : X ⟶ OptionSyntax.obj Y) :
    (Subobject.pullback (f ≫ optionTag Y)).obj (Subobject.mk (Two.point (C := C) true)) =
      OptionSyntax.success f := by
  rw [OptionSyntax.success_eq_mk]
  exact Subobject.pullback_obj_mk (optionTag_success_isPullback f).flip

end CategoricalEssentialIncompleteness.V46.SyntaxOptionTransport
