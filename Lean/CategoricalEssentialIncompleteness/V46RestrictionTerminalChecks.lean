/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RestrictionTerminal
public import CategoricalEssentialIncompleteness.V46SplitSplittings

/-! # Restriction-terminal laws under the split total-category hypothesis -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46 RestrictionTerminal RestrictionSubobjects

variable {C : Type u} [Category.{v} C] [RestrictionCategory C]

example [Splits C] {Z : Tot C} (hZ : IsTerminal Z) {X Y : C} (f : X ⟶ Y) :
    isTotal (terminate hZ X) ∧ terminate hZ Z.obj = 𝟙 Z.obj ∧
      f ≫ terminate hZ Y = rst f ≫ terminate hZ X :=
  ⟨terminate_total hZ X, terminate_self hZ, terminate_naturality hZ f⟩

example [HasTerminal (Tot (SplitObject C))] :
    ∃ (Z : SplitObject C) (t : ∀ X : SplitObject C, X ⟶ Z),
      (∀ X, isTotal (t X)) ∧ t Z = 𝟙 Z ∧
      (∀ {X Y : SplitObject C} (f : X ⟶ Y), f ≫ t Y = rst f ≫ t X) :=
  exists_restriction_terminal

#print axioms CategoricalEssentialIncompleteness.V46.RestrictionTerminal.terminate_total
#print axioms CategoricalEssentialIncompleteness.V46.RestrictionTerminal.terminate_self
#print axioms CategoricalEssentialIncompleteness.V46.RestrictionTerminal.terminate_unique
#print axioms CategoricalEssentialIncompleteness.V46.RestrictionTerminal.terminate_naturality
#print axioms CategoricalEssentialIncompleteness.V46.RestrictionTerminal.exists_restriction_terminal
