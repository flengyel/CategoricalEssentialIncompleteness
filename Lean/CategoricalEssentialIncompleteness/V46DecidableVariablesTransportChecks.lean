/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DecidableVariablesTransport

/-! Transport of the actual diagonal pullback, with independent universe levels. -/

@[expose] public section
noncomputable section
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [HasFiniteLimits C] [HasFiniteCoproducts C]
variable [HasFiniteLimits D] [HasFiniteCoproducts D]

example (E : C ≌ D) {V : C} (S : DecidableVariables V)
    (W : D) (e : E.functor.obj V ≅ W) : DecidableVariables W :=
  DecidableVariables.Transport.mapped E S W e

example (E : C ≌ D) {V : C} (S : DecidableVariables V)
    (W : D) (e : E.functor.obj V ≅ W) :
    IsPullback (prod.lift (𝟙 W) (𝟙 W)) (terminal.from W)
      (DecidableVariables.Transport.mapped E S W e).test
      (coprod.inr : ⊤_ D ⟶ (⊤_ D) ⨿ (⊤_ D)) :=
  (DecidableVariables.Transport.mapped E S W e).diagonal
