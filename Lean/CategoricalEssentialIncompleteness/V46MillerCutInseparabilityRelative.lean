/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCutInseparability


/-! # Definitions and theorems in `V46MillerCutInseparabilityRelative` -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # The fixed-oracle separator obstructs Turing universality of J_p(tau)

This is a consequence of the displayed recursive reduction;
CutApplications supplies the actual reduction proved in Lemma8.3. Its target is the full fixed-oracle category, not the earlier
restricted category of ordinary value extensions.
-/
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.Miller.CutInseparability

open _root_.CategoricalEssentialIncompleteness.V46.Miller.Uniform
attribute [instance 2000] Uniform.nativeRestriction

def fixedDecision (p : Bits) : N (Family.singleton p) ⟶ N (Family.singleton p) :=
  ⟨fun n => Part.some (CutDigits.decision p n),⟨CutDigits.decisionIndex,by
    intro q hq n y
    have he : q=p := Set.mem_singleton_iff.mp hq
    subst q
    exact Iff.of_eq (congrArg (fun v : Part ℕ => y ∈ v)
      (CutDigits.decisionIndex_eval p n).symm)⟩⟩

def preimageDecision (p : Bits) (h : ℕ → ℕ) (hh : Computable h) :
    N (Family.singleton p) ⟶ N (Family.singleton p) :=
  Uniform.totalFromFunction (X:=N (Family.singleton p)) (Y:=N (Family.singleton p)) h hh ≫ fixedDecision p

theorem preimageDecision_value (p : Bits) (h : ℕ → ℕ) (hh : Computable h) (e : ℕ) :
    (preimageDecision p h hh).val e = Part.some (CutDigits.decision p (h e)) := by
  change (Part.some (h e)).bind (fun n => Part.some (CutDigits.decision p n)) = _
  exact Part.bind_some ..

theorem decisionPredicate_enumerable (p : Bits) (h : ℕ → ℕ) (hh : Computable h) (b : ℕ) :
    Enumerable (Family.singleton p) (fun e => CutDigits.decision p (h e)=b) := by
  have hgraph := Enumerable.comp (Computable.pair Computable.id (Computable.const b))
    (Uniform.graph_enumerable (preimageDecision p h hh))
  apply hgraph.of_eq
  intro e
  rw [preimageDecision_value]
  exact Part.mem_some_iff.trans eq_comm

def fixedGuard (p : Bits) (h : ℕ → ℕ) (hh : Computable h) (b : ℕ) :
    Idem (N (Family.singleton p)) :=
  Uniform.setIdem _ {e | CutDigits.decision p (h e)=b}
    (decisionPredicate_enumerable p h hh b)

@[simp] theorem fixedGuard_support (p : Bits) (h : ℕ → ℕ) (hh : Computable h) (b : ℕ) :
    Uniform.support (fixedGuard p h hh b) = {e | CutDigits.decision p (h e)=b} :=
  Uniform.support_setIdem _ _ _

theorem fixedGuard_complementary (p : Bits) (h : ℕ → ℕ) (hh : Computable h) :
    Complementary (fixedGuard p h hh 1) (fixedGuard p h hh 0) := by
  constructor
  · apply Uniform.toPfnIdem_injective
    apply PartialFunctions.support_injective
    rw [Uniform.toPfnIdem_inf,Uniform.toPfnIdem_bot,PartialFunctions.support_inf,
      PartialFunctions.support_bot]
    change {e | CutDigits.decision p (h e)=1} ∩ {e | CutDigits.decision p (h e)=0} = ∅
    ext e
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Set.notMem_empty,iff_false]
    omega
  · apply Uniform.toPfnIdem_injective
    apply PartialFunctions.support_injective
    rw [Uniform.toPfnIdem_sup,Uniform.toPfnIdem_top,PartialFunctions.support_sup,
      PartialFunctions.support_top]
    change {e | CutDigits.decision p (h e)=1} ∪ {e | CutDigits.decision p (h e)=0} = Set.univ
    ext e
    simp only [Set.mem_union,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
    have hb := CutDigits.decision_le_one p (h e)
    omega

def mappedTau (z : Point) (p : Bits) (hp : p ∈ representations z) :
    product (N (Family.singleton p)) (N (Family.singleton p)) ⟶ N (Family.singleton p) :=
  (Uniform.J z p hp).toFunctor.map (Uniform.tau z)

theorem mapped_pair0_support (z : Point) (p : Bits) (hp : p ∈ representations z) :
    Uniform.support (pair0 (mappedTau z p hp)) = Uniform.support (diagonal0 z) := by
  ext e
  exact (support_pair0 (mappedTau z p hp) e).trans (diagonal0_support z e).symm

theorem mapped_pair1_support (z : Point) (p : Bits) (hp : p ∈ representations z) :
    Uniform.support (pair1 (mappedTau z p hp)) = Uniform.support (diagonal1 z) := by
  ext e
  exact (support_pair1 (mappedTau z p hp) e).trans (diagonal1_support z e).symm

/-- The source evaluator's image is not made universal by passing to a
fixed representation. The full target does have its separate oracleTau.
Its recursive-reduction premise is discharged in CutApplications. -/
theorem mapped_tau_notTuring_of_recursive_reduction
    (z : Point) (h : ℕ → ℕ) (hh : Computable h)
    (h₀ : h ⁻¹' CutDigits.lowerCut z = Uniform.support (diagonal0 z))
    (h₁ : h ⁻¹' CutDigits.upperCut z = Uniform.support (diagonal1 z))
    (p : Bits) (hp : p ∈ representations z) :
    ¬RecursionCategory.IsTuringMorphism ((Uniform.J z p hp).toFunctor.map (Uniform.tau z)) := by
  intro hT
  have hi := turing_pair_inseparable (mappedTau z p hp) hT
  have hsep := CutDigits.separates_point z p hp
  apply hi.no_separator
  refine ⟨fixedGuard p h hh 1,fixedGuard p h hh 0,fixedGuard_complementary p h hh,?_,?_⟩
  · apply (Uniform.support_le_iff _ _).mpr
    intro e he
    rw [mapped_pair0_support] at he
    have hL : h e ∈ CutDigits.lowerCut z := (Set.ext_iff.mp h₀ e).mpr he
    exact (CutDigits.decision_one_iff p (h e)).mpr (hsep.1 hL)
  · apply (Uniform.support_le_iff _ _).mpr
    intro e he
    rw [mapped_pair1_support] at he
    have hR : h e ∈ CutDigits.upperCut z := (Set.ext_iff.mp h₁ e).mpr he
    have hn : h e ∉ CutDigits.separator p := fun hm => Set.disjoint_left.mp hsep.2 hm hR
    have hb := CutDigits.decision_le_one p (h e)
    have hn' : CutDigits.decision p (h e)≠1 := fun hm =>
      hn ((CutDigits.decision_one_iff p (h e)).mp hm)
    change CutDigits.decision p (h e)=0
    omega

end CategoricalEssentialIncompleteness.V46.Miller.CutInseparability
