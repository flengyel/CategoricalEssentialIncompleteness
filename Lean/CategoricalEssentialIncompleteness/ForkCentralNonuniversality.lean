/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EffectiveForkEvaluation
import CategoricalEssentialIncompleteness.EffectiveForkProbes

/-! # Central evaluation does not preserve the selected Turing universality -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open EnumerableCarriers (val)

/-- The displayed map (k,z,a,b) ↦ (0,0,z,0). -/
def hiddenShift (x : ℕ) : ℕ := quadCode (0,0,(quadCode.symm x).2.1,0)

theorem hiddenShift_computable : Computable hiddenShift :=
  quadCode_computable.comp (Computable.pair (.const 0) (Computable.pair (.const 0)
    (Computable.pair ((Computable.fst.comp Computable.snd).comp quadDecode_computable) (.const 0))))

theorem hiddenShift_quad (k z a b : ℕ) :
    hiddenShift (quadCode (k,z,a,b))=quadCode (0,0,z,0) := by
  unfold hiddenShift
  rw [Equiv.symm_apply_apply]

theorem leftCoordinate_quad (k z a b : ℕ) :
    leftCoordinate (quadCode (k,z,a,b))=Nat.pair k a := by
  simp only [leftCoordinate,quadCode,Equiv.coe_fn_mk,Nat.unpair_pair]

theorem no_center_parameter (p : ℕ) :
    ¬ ∀ x,hiddenShift x ∈ centerEval (Nat.pair p x) := by
  intro h
  let x0 := quadCode (0,0,0,0)
  let x1 := quadCode (0,1,0,0)
  have h0 := ((mem_centerEval _ _).mp (h x0)).2.1
  have h1 := ((mem_centerEval _ _).mp (h x1)).2.1
  have he : leftEval (Nat.pair p x0)=leftEval (Nat.pair p x1) := by
    simp [leftEval,leftCoordinate,quadCode,x0,x1]
  rw [← he] at h1
  have hh := Part.mem_unique h0 h1
  dsimp only [x0,x1] at hh
  simp only [hiddenShift_quad,leftCoordinate_quad] at hh
  have hz := congrArg (fun n => (Nat.unpair n).2) hh
  simp only [Nat.unpair_pair] at hz
  exact Nat.zero_ne_one hz

def hiddenMap : EnumerableCarriers.product singletonCarrier natCarrier ⟶ natCarrier :=
  EnumerableCarriers.totalFromFunction (fun n => hiddenShift (Nat.unpair n).2)
    (hiddenShift_computable.comp (Computable.snd.comp Computable.unpair))
    (fun n _ => Set.mem_univ (hiddenShift (Nat.unpair n).2))

theorem center_not_isTuring : ¬ RecursionCategory.IsTuringMorphism centerEvaluator := by
  intro h
  obtain ⟨r,hr,he⟩ := h singletonCarrier hiddenMap
  have ht : isTotal r := by
    change RestrictionCategory.rst r=𝟙 _
    rw [← carrier_induced_restriction]
    exact hr
  obtain ⟨p,hp⟩ := Part.dom_iff_mem.mp ((EnumerableCarriers.total_iff r).mp ht 0 rfl)
  apply no_center_parameter p
  intro x
  have hm : hiddenShift x ∈ val hiddenMap (Nat.pair 0 x) :=
    (EnumerableCarriers.mem_totalFromFunction _ _ _ _ _).mpr
      ⟨⟨by simp [singletonCarrier],Set.mem_univ _⟩,by simp⟩
  rw [← he] at hm
  obtain ⟨k,hk,hm⟩ := (EnumerableCarriers.mem_val_comp _ _ _ _).mp hm
  obtain ⟨hk0,hk1⟩ := (EnumerableCarriers.mem_partialProdMap_iff r (𝟙 natCarrier) _ _).mp hk
  simp only [Nat.unpair_pair] at hk0 hk1
  have hk0 := Part.mem_unique hk0 hp
  have hk1 := ((mem_supportIdentity natCarrier.support _ _).mp hk1).2
  have hk : k=Nat.pair p x := by rw [← hk0,← hk1,Nat.pair_unpair]
  change hiddenShift x ∈ centerEval k at hm
  rwa [hk] at hm

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
