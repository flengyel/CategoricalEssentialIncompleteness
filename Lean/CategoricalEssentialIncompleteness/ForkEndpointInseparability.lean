/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EffectiveForkEvaluation
import CategoricalEssentialIncompleteness.EffectiveForkCoproductFrame
import CategoricalEssentialIncompleteness.EffectiveForkRecursion
import CategoricalEssentialIncompleteness.EnumerableLocalConnectedness
import CategoricalEssentialIncompleteness.CompatibleLocalLifting

/-! # The actual endpoint diagonal pair is numerically inseparable -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts

namespace CategoricalEssentialIncompleteness.LocalConnectedness

namespace EnumerableCarriers

def identityRangeFunctor : RangeFunctor Carrier Carrier where
  toFunctor := 𝟭 Carrier
  map_restrict _ := rfl
  map_range _ := rfl
  map_zero _ _ := rfl
  comparison_isIso X Y := by
    change IsIso (copair (i0 X Y) (i1 X Y))
    rw [copair_i0_i1]
    infer_instance

theorem identity_section_lifting {U : Carrier} :
    ∀ (c c' : Idem U) (hc : Complementary c c'),∃ l : U ⟶ coprod U U,
      identityRangeFunctor.toFunctor.map l=
        switchSection (identityRangeFunctor.mapIdem c) (identityRangeFunctor.mapIdem c')
          (identityRangeFunctor.map_complementary hc) ≫
          (identityRangeFunctor.comparison U U).hom := by
  intro c c' hc
  exact ⟨_,rfl⟩

end EnumerableCarriers

namespace EffectiveFork

open EnumerableCarriers (Carrier val)

def endpointFrame : natCarrier ≅ coprod natCarrier natCarrier where
  hom := coproductFrame.hom.left
  inv := coproductFrame.inv.left
  hom_inv_id := congrArg Hom.left coproductFrame.hom_inv_id
  inv_hom_id := congrArg Hom.left coproductFrame.inv_hom_id

def endpointPair0 : Idem natCarrier :=
  Idem.pull (EnumerableCarriers.partialDiag natCarrier ≫ endpointEvaluator ≫ endpointFrame.hom)
    (summand0 natCarrier natCarrier)
def endpointPair1 : Idem natCarrier :=
  Idem.pull (EnumerableCarriers.partialDiag natCarrier ≫ endpointEvaluator ≫ endpointFrame.hom)
    (summand1 natCarrier natCarrier)

theorem endpoint_identity_nonzero :
    EnumerableCarriers.identityRangeFunctor.toFunctor.map (𝟙 natCarrier)≠0 := by
  intro h
  have hh := congrArg (fun f => val f 0) h
  have h0 : 0 ∈ val (𝟙 natCarrier) 0 :=
    (mem_supportIdentity Set.univ 0 0).mpr ⟨Set.mem_univ _,rfl⟩
  change val (𝟙 natCarrier) 0=Part.none at hh
  rw [hh] at h0
  exact h0.1

/-- Numerical local connectedness and the actual endpoint Turing morphism
instantiate the same categorical lifting theorem as the internal construction. -/
theorem endpoint_pair_inseparable : Inseparable endpointPair0 endpointPair1 :=
  compatible_local_lifting EnumerableCarriers.inducedRestriction_eq
    EnumerableCarriers.identityRangeFunctor endpointEvaluator endpoint_isTuring endpointFrame
    endpoint_identity_nonzero EnumerableCarriers.identity_section_lifting

theorem left_pair0 : leftIdem (Recursion.toIdem Recursion.pair0)=endpointPair0 := by
  change leftIdem (Recursion.toIdem (Idem.pull _ _))=_
  rw [Recursion.toIdem_pull]
  rfl

theorem left_pair1 : leftIdem (Recursion.toIdem Recursion.pair1)=endpointPair1 := by
  change leftIdem (Recursion.toIdem (Idem.pull _ _))=_
  rw [Recursion.toIdem_pull]
  rfl

theorem right_pair0 : rightIdem (Recursion.toIdem Recursion.pair0)=endpointPair0 := by
  change rightIdem (Recursion.toIdem (Idem.pull _ _))=_
  rw [Recursion.toIdem_pull]
  rfl

theorem right_pair1 : rightIdem (Recursion.toIdem Recursion.pair1)=endpointPair1 := by
  change rightIdem (Recursion.toIdem (Idem.pull _ _))=_
  rw [Recursion.toIdem_pull]
  rfl

theorem left_pair_inseparable :
    Inseparable (leftIdem (Recursion.toIdem Recursion.pair0))
      (leftIdem (Recursion.toIdem Recursion.pair1)) := by
  rw [left_pair0,left_pair1]
  exact endpoint_pair_inseparable

theorem right_pair_inseparable :
    Inseparable (rightIdem (Recursion.toIdem Recursion.pair0))
      (rightIdem (Recursion.toIdem Recursion.pair1)) := by
  rw [right_pair0,right_pair1]
  exact endpoint_pair_inseparable

end EffectiveFork
end CategoricalEssentialIncompleteness.LocalConnectedness
