/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46BooleanSquare

/-! The Boolean square is a genuine product, compared with four terminal summands. -/

@[expose] public section
noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

example : ((⊤_ D) ⨿ (⊤_ D)) ⨿ ((⊤_ D) ⨿ (⊤_ D)) ≅
    ((⊤_ D) ⨿ (⊤_ D)) ⨯ ((⊤_ D) ⨿ (⊤_ D)) := BooleanSquare.iso

example (a b : Bool) : BooleanSquare.point (D := D) a b ≫ BooleanSquare.iso.hom =
    prod.lift (Two.point a) (Two.point b) := BooleanSquare.point_encode a b

example (a b : Bool) :
    prod.lift (Two.point (C := D) a) (Two.point b) ≫ BooleanSquare.iso.inv =
      BooleanSquare.point a b := BooleanSquare.pairPoint_decode a b
