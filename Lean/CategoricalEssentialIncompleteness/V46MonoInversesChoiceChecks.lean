/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MonoInversesChoice

/-! # The partial-inverse hypothesis implies weak choice without a range premise -/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.RestrictionSubobjects

variable {C : Type u} [Category.{v} C] [RestrictionCategory C] [Splits C]

example (h : MonoInverses C) {X Y : C} (p : X ⟶ Y) (hp : PartialMono p) :
    ∃ s : Y ⟶ X, s ≫ p = rst s ∧ p ≫ s ≫ p = p := by
  obtain ⟨s, hs⟩ := section_of_partial_mono h p hp
  exact ⟨s, hs.comp, hs.receives⟩

example (h : MonoInverses C) : WeakChoice C := weakChoice h

#print axioms CategoricalEssentialIncompleteness.V46.RestrictionSubobjects.section_of_partial_mono
#print axioms CategoricalEssentialIncompleteness.V46.RestrictionSubobjects.weakChoice
