/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RestrictionSubobjects
public import CategoricalEssentialIncompleteness.V46SubobjectInseparability

/-! # The subobject and restriction-idempotent notions of inseparability -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.RestrictionSubobjects

variable {C : Type u} [Category.{v} C] [RestrictionCategory C]
variable [Splits C] [HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C]
variable [Regular (Tot C)] [FinitaryExtensive (Tot C)]
variable (h : MonoInverses C) {X : Tot C}

theorem complementary_iff (a b : Subobject X) :
    Complementary (domain h a) (domain h b) ↔ IsCompl a b := by
  let e := orderIso h X
  have he (A : Subobject X) : e A = domain h A := rfl
  constructor
  · intro hc
    constructor
    · apply disjoint_iff.mpr
      apply e.injective
      simpa only [e.map_inf, e.map_bot, he] using hc.disjoint
    · apply codisjoint_iff.mpr
      apply e.injective
      simpa only [e.map_sup, e.map_top, he] using hc.cover
  · intro hc
    constructor
    · simpa only [e.map_inf, e.map_bot, he] using congrArg e hc.inf_eq_bot
    · simpa only [e.map_sup, e.map_top, he] using congrArg e hc.sup_eq_top

theorem inseparable_iff (a b : Subobject X) :
    Inseparable (domain h a) (domain h b) ↔ SubobjectInseparable a b := by
  let e := orderIso h X
  have he (A : Subobject X) : e A = domain h A := rfl
  constructor
  · intro hi
    refine ⟨?_, ?_⟩
    · apply e.injective
      simpa only [e.map_inf, e.map_bot, he] using hi.disjoint
    · rintro ⟨p, ha, hb⟩
      exact hi.no_separator ⟨domain h p.positive, domain h p.negative,
        (complementary_iff h _ _).mpr p.complementary,
        (domain_le_iff h _ _).mpr ha, (domain_le_iff h _ _).mpr hb⟩
  · rintro ⟨hd, hs⟩
    refine ⟨?_, ?_⟩
    · simpa only [e.map_inf, e.map_bot, he] using congrArg e hd
    · rintro ⟨c, c', hc, ha, hb⟩
      have hp : Complementary (domain h (e.symm c)) (domain h (e.symm c')) := by
        change Complementary (e (e.symm c)) (e (e.symm c'))
        simpa only [e.apply_symm_apply] using hc
      apply hs
      refine ⟨⟨e.symm c, e.symm c', (complementary_iff h _ _).mp hp⟩, ?_, ?_⟩
      · apply (domain_le_iff h _ _).mp
        change e a ≤ e (e.symm c)
        simpa only [e.apply_symm_apply, he] using ha
      · apply (domain_le_iff h _ _).mp
        change e b ≤ e (e.symm c')
        simpa only [e.apply_symm_apply, he] using hb

end CategoricalEssentialIncompleteness.V46.RestrictionSubobjects
