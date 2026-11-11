/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkNumericalProofs
public import CategoricalEssentialIncompleteness.EffectiveForkSplitting

/-! # The actual fork of finite proofs and its natural conclusion morphism -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax

open EffectiveFork (Object V centerIdem leftIdem rightIdem)
open EnumerableCarriers (support support_re val)

theorem mem_proofMap {A B A' B' : Set ℕ}
    (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (hA' : REPred (· ∈ A')) (hB' : REPred (· ∈ B'))
    (f : ℕ → ℕ) (hf : Computable f)
    (ha : ∀ x ∈ A,f x ∈ A') (hb : ∀ x ∈ B,f x ∈ B') (x y : ℕ) :
    y ∈ val (proofMap hA hB hA' hB' f hf ha hb) x ↔
      x ∈ (proofCarrier A B hA hB).support ∧ y=proofRelabelCode f x :=
  EnumerableCarriers.mem_totalFromFunction _ _ _ x y

theorem conclusion_respects {A B A' B' : Set ℕ}
    (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (hA' : REPred (· ∈ A')) (hB' : REPred (· ∈ B'))
    (f : ℕ → ℕ) (hf : Computable f)
    (ha : ∀ x ∈ A,f x ∈ A') (hb : ∀ x ∈ B,f x ∈ B') :
    EffectiveFork.Respects (proofMap hA hB hA' hB' f hf ha hb)
      (natArrow (Formula.sigma f) (Formula.sigma_computable hf))
      (conclusionArrow A B hA hB) (conclusionArrow A' B' hA' hB') := by
  intro x y u v hxy hxu hyv
  obtain ⟨hx,rfl⟩ := (EnumerableCarriers.mem_totalFromFunction conclusionCode
    conclusionCode_computable (fun x _ => Set.mem_univ (conclusionCode x)) x y).mp hxy
  obtain ⟨_,rfl⟩ := (mem_proofMap hA hB hA' hB' f hf ha hb x u).mp hxu
  apply (EnumerableCarriers.mem_totalFromFunction conclusionCode conclusionCode_computable
    (fun x _ => Set.mem_univ (conclusionCode x)) _ v).mpr
  refine ⟨(mem_proofCarrier A' B' hA' hB' _).mpr
    (proofRelabel_valid f ha hb x ((mem_proofCarrier A B hA hB x).mp hx)),?_⟩
  rw [conclusion_relabel f ha hb x ((mem_proofCarrier A B hA hB x).mp hx)]
  exact (mem_natArrow _ _ _ v).mp hyv

theorem left_axioms (a : Idem V) :
    ∀ x ∈ support (centerIdem a),
      EffectiveFork.leftCoordinate x ∈ support (leftIdem a) := by
  intro x hx
  exact EffectiveFork.closed_left a x _ hx ((EffectiveFork.mem_V_left _ _).mpr rfl)

theorem right_axioms (a : Idem V) :
    ∀ x ∈ support (centerIdem a),
      EffectiveFork.rightCoordinate x ∈ support (rightIdem a) := by
  intro x hx
  exact EffectiveFork.closed_right a x _ hx ((EffectiveFork.mem_V_right _ _).mpr rfl)

def Prf (a b : Idem V) : Object where
  center := proofCarrier (support (centerIdem a)) (support (centerIdem b))
    (support_re _) (support_re _)
  left := proofCarrier (support (leftIdem a)) (support (leftIdem b))
    (support_re _) (support_re _)
  right := proofCarrier (support (rightIdem a)) (support (rightIdem b))
    (support_re _) (support_re _)
  leftMap := proofMap (support_re _) (support_re _) (support_re _) (support_re _)
    EffectiveFork.leftCoordinate EffectiveFork.leftCoordinate_computable
    (left_axioms a) (left_axioms b)
  rightMap := proofMap (support_re _) (support_re _) (support_re _) (support_re _)
    EffectiveFork.rightCoordinate EffectiveFork.rightCoordinate_computable
    (right_axioms a) (right_axioms b)
  left_total := proofMap_total _ _ _ _ _ _ _ _
  right_total := proofMap_total _ _ _ _ _ _ _ _

def conclusion (a b : Idem V) : Prf a b ⟶ S where
  center := conclusionArrow _ _ (support_re _) (support_re _)
  left := conclusionArrow _ _ (support_re _) (support_re _)
  right := conclusionArrow _ _ (support_re _) (support_re _)
  natural_left := conclusion_respects _ _ _ _ _ EffectiveFork.leftCoordinate_computable
    (left_axioms a) (left_axioms b)
  natural_right := conclusion_respects _ _ _ _ _ EffectiveFork.rightCoordinate_computable
    (right_axioms a) (right_axioms b)

theorem conclusion_total (a b : Idem V) : isTotal (conclusion a b) :=
  (EffectiveFork.total_iff _).mpr ⟨
    conclusionArrow_total (support (centerIdem a)) (support (centerIdem b)) _ _,
    conclusionArrow_total (support (leftIdem a)) (support (leftIdem b)) _ _,
    conclusionArrow_total (support (rightIdem a)) (support (rightIdem b)) _ _⟩

def t0 (a b : Idem V) : Idem S := Ranges.range (conclusion a b)

theorem center_t0 (a b : Idem V) (n : ℕ) :
    n ∈ support (centerIdem (t0 a b)) ↔
      Formula.decode n ∈ Theorems (support (centerIdem a)) (support (centerIdem b)) :=
  conclusion_range (support (centerIdem a)) (support (centerIdem b)) _ _ n

theorem left_t0 (a b : Idem V) (n : ℕ) :
    n ∈ support (leftIdem (t0 a b)) ↔
      Formula.decode n ∈ Theorems (support (leftIdem a)) (support (leftIdem b)) :=
  conclusion_range (support (leftIdem a)) (support (leftIdem b)) _ _ n

theorem right_t0 (a b : Idem V) (n : ℕ) :
    n ∈ support (rightIdem (t0 a b)) ↔
      Formula.decode n ∈ Theorems (support (rightIdem a)) (support (rightIdem b)) :=
  conclusion_range (support (rightIdem a)) (support (rightIdem b)) _ _ n

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax
