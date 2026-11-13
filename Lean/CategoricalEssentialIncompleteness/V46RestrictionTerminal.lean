/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RestrictionSubobjects
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! # Restriction terminal objects from terminal objects of the total category -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.RestrictionTerminal

open RestrictionSubobjects

variable {C : Type u} [Category.{v} C] [RestrictionCategory C]
variable {Z : Tot C} (hZ : IsTerminal Z)

def terminate (X : C) : X ⟶ Z.obj := (hZ.from (⟨X⟩ : Tot C)).hom

theorem terminate_total (X : C) : isTotal (terminate hZ X) :=
  (hZ.from (⟨X⟩ : Tot C)).property

theorem terminate_self : terminate hZ Z.obj = 𝟙 Z.obj :=
  congrArg (fun k => k.hom) (hZ.hom_ext (hZ.from Z) (𝟙 Z))

theorem terminate_unique {X : C} (f : X ⟶ Z.obj) (hf : isTotal f) :
    f = terminate hZ X :=
  congrArg (fun k => k.hom) (hZ.hom_ext (⟨f, hf⟩ : (⟨X⟩ : Tot C) ⟶ Z) (hZ.from ⟨X⟩))

variable [Splits C]

/-- Partial naturality follows by splitting the domain of the morphism. -/
theorem terminate_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ terminate hZ Y = rst f ≫ terminate hZ X := by
  obtain ⟨A, m, r, hm, hmr, hrm⟩ := Splits.splitting (Idem.ofRestrict f)
  change r ≫ m = rst f at hrm
  have hma : m ≫ rst f = m := by
    rw [← hrm, ← Category.assoc, hmr, Category.id_comp]
  have hq : isTotal (m ≫ f) := by
    change rst (m ≫ f) = 𝟙 A
    rw [rst_comp_rst_right, hma]
    exact hm
  have he : m ≫ terminate hZ X = (m ≫ f) ≫ terminate hZ Y := by
    exact congrArg (fun k => k.hom)
      (hZ.hom_ext
        ((⟨m, hm⟩ : (⟨A⟩ : Tot C) ⟶ ⟨X⟩) ≫ hZ.from ⟨X⟩)
        ((⟨m ≫ f, hq⟩ : (⟨A⟩ : Tot C) ⟶ ⟨Y⟩) ≫ hZ.from ⟨Y⟩))
  calc
    _ = (r ≫ (m ≫ f)) ≫ terminate hZ Y := by
      rw [← Category.assoc r m f, hrm, rst_comp_self]
    _ = r ≫ (m ≫ terminate hZ X) := by rw [Category.assoc, ← he]
    _ = rst f ≫ terminate hZ X := by rw [← Category.assoc, hrm]

theorem exists_restriction_terminal [HasTerminal (Tot C)] :
    ∃ (Z : C) (t : ∀ X : C, X ⟶ Z),
      (∀ X, isTotal (t X)) ∧ t Z = 𝟙 Z ∧
      (∀ {X Y : C} (f : X ⟶ Y), f ≫ t Y = rst f ≫ t X) :=
  ⟨(⊤_ (Tot C)).obj, terminate terminalIsTerminal,
    terminate_total terminalIsTerminal, terminate_self terminalIsTerminal,
    terminate_naturality terminalIsTerminal⟩

end CategoricalEssentialIncompleteness.V46.RestrictionTerminal
