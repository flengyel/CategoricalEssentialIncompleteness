/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SignedFirstOrderCategories

/-! # Statement checks for the free first-order adjunction -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D}
variable (F : NullaryPresentations V)
open SignedFirstOrder

example : Pair F ⥤ Theories (D := D) (V := V) := generation F
example : Theories (D := D) (V := V) ⥤ Pair F := extraction F

#print axioms CategoricalEssentialIncompleteness.V46.SignedFirstOrder.generation
#print axioms CategoricalEssentialIncompleteness.V46.SignedFirstOrder.extraction
#print axioms CategoricalEssentialIncompleteness.V46.SignedFirstOrder.extractionObject
