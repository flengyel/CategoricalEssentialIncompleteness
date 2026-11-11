/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ModelLogicalSoundness


/-! # Statement checks in `V46ModelLogicalSoundnessChecks` -/

@[expose] public section
noncomputable section
universe v u w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ModelLogicalSoundnessChecks
open ModelLogicalSoundness
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable (G : C ⥤ Type w) {Fm : C}
variable (imp : Fm ⨯ Fm ⟶ Fm) (P : G.obj Fm → Prop)
variable (himp : ∀ z : G.obj (Fm ⨯ Fm), P (G.map imp z) ↔
  (P (G.map (prod.fst : Fm ⨯ Fm ⟶ Fm) z) → P (G.map (prod.snd : Fm ⨯ Fm ⟶ Fm) z)))
include himp

example (z : G.obj (Fm ⨯ Fm)) :
    P (G.map (prod.lift prod.fst (prod.lift prod.snd prod.fst ≫ imp) ≫ imp) z) :=
  valid_one G imp P himp z
example (neg : Fm ⟶ Fm)
    (hneg : ∀ φ : G.obj Fm, P (G.map neg φ) ↔ ¬ P φ) (z : G.obj (Fm ⨯ Fm)) :
    P (G.map (prod.lift
      (prod.lift (prod.snd ≫ neg) (prod.fst ≫ neg) ≫ imp) imp ≫ imp) z) :=
  valid_three G imp P himp neg hneg z
end CategoricalEssentialIncompleteness.V46.ModelLogicalSoundnessChecks
