/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.RestrictionSplitting
import CategoricalEssentialIncompleteness.LocalSwitch

/-! # Every restriction idempotent splits in the restriction splitting -/

universe v u

open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.SplitObject

variable {C : Type u} [Category.{v} C] [RestrictionCategory C]

instance splitSplits : Splits (SplitObject C) where
  splitting {X} a := by
    let Z : SplitObject C := ⟨X.base, baseIdem a⟩
    have hid : a.hom.hom ≫ a.hom.hom = a.hom.hom := congrArg Hom.hom a.idem
    let m : Z ⟶ X := ⟨a.hom.hom, hid, a.hom.target⟩
    let r : X ⟶ Z := ⟨a.hom.hom, a.hom.source, hid⟩
    refine ⟨Z, m, r, ?_, Hom.ext hid, Hom.ext hid⟩
    apply Hom.ext
    change rst a.hom.hom = a.hom.hom
    exact congrArg Hom.hom a.restriction

end CategoricalEssentialIncompleteness.LocalConnectedness.SplitObject
