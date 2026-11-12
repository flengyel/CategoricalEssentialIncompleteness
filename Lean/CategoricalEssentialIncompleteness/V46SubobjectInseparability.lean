/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46BooleanFibers

/-! # Complementary-subobject separators -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {X Y : D}

def HasSubobjectSeparator (a b : Subobject X) : Prop :=
  ∃ p : SubobjectPartition X, a ≤ p.positive ∧ b ≤ p.negative

def SubobjectInseparable (a b : Subobject X) : Prop :=
  a ⊓ b = ⊥ ∧ ¬ HasSubobjectSeparator a b

theorem subobject_separator_iff_boolean (a b : Subobject X) :
    HasSubobjectSeparator a b ↔ ∃ d : X ⟶ Two D,
      a.arrow ≫ d = Two.constant _ true ∧ b.arrow ≫ d = Two.constant _ false := by
  constructor
  · rintro ⟨p, ha, hb⟩
    refine ⟨p.characteristic, ?_, ?_⟩
    · apply (Two.le_fiber_iff a p.characteristic true).mp
      change a ≤ boundFiber p.characteristic (Two.point true)
      rw [p.characteristic_positive]
      exact ha
    · apply (Two.le_fiber_iff b p.characteristic false).mp
      change b ≤ boundFiber p.characteristic (Two.point false)
      rw [p.characteristic_negative]
      exact hb
  · rintro ⟨d, ha, hb⟩
    exact ⟨⟨Two.fiberSubobject d true, Two.fiberSubobject d false,
      (Two.boundFibers_isCompl d).symm⟩,
      (Two.le_fiber_iff a d true).mpr ha, (Two.le_fiber_iff b d false).mpr hb⟩

theorem subobject_separator_pullback (f : X ⟶ Y) {a b : Subobject Y}
    (h : HasSubobjectSeparator a b) :
    HasSubobjectSeparator ((Subobject.pullback f).obj a) ((Subobject.pullback f).obj b) := by
  obtain ⟨p, ha, hb⟩ := h
  exact ⟨⟨(Subobject.pullback f).obj p.positive, (Subobject.pullback f).obj p.negative,
      (ComplementaryPair.map (SubobjectPredicates.pullbackHom f)
        ⟨p.positive, p.negative, p.complementary⟩).compl⟩,
    (Subobject.pullback f).monotone ha, (Subobject.pullback f).monotone hb⟩

omit [Regular D] in
theorem subobject_separator_mono {a b c d : Subobject X}
    (ha : a ≤ c) (hb : b ≤ d) (h : HasSubobjectSeparator c d) :
    HasSubobjectSeparator a b := by
  obtain ⟨p, hc, hd⟩ := h
  exact ⟨p, ha.trans hc, hb.trans hd⟩

end CategoricalEssentialIncompleteness.V46
