/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EffectiveForkCoproducts
public import CategoricalEssentialIncompleteness.EffectiveForkProbes
public import CategoricalEssentialIncompleteness.ForkObstruction

/-! # The universal fork, with recursively coded tuple carriers -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open EnumerableCarriers (Carrier val)

def natCarrier : Carrier := ⟨Set.univ, REPred.const True⟩

def quadCode : (ℕ × ℕ × ℕ × ℕ) ≃ ℕ where
  toFun x := Nat.pair x.1 (Nat.pair x.2.1 (Nat.pair x.2.2.1 x.2.2.2))
  invFun n := ((Nat.unpair n).1, (Nat.unpair (Nat.unpair n).2).1,
    (Nat.unpair (Nat.unpair (Nat.unpair n).2).2).1,
    (Nat.unpair (Nat.unpair (Nat.unpair n).2).2).2)
  left_inv x := by rcases x with ⟨k,z,a,b⟩; simp
  right_inv n := by simp [Nat.pair_unpair]

theorem quadCode_computable : Computable quadCode :=
  Primrec₂.natPair.to_comp.comp Computable.fst
    (Primrec₂.natPair.to_comp.comp (Computable.fst.comp Computable.snd)
      (Primrec₂.natPair.to_comp.comp
        (Computable.fst.comp (Computable.snd.comp Computable.snd))
        (Computable.snd.comp (Computable.snd.comp Computable.snd))))

theorem quadDecode_computable : Computable quadCode.symm :=
  Computable.pair (Computable.fst.comp Computable.unpair)
    (Computable.pair
      (Computable.fst.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair)))
      (Computable.pair
        (Computable.fst.comp (Computable.unpair.comp (Computable.snd.comp
          (Computable.unpair.comp (Computable.snd.comp Computable.unpair)))))
        (Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp
          (Computable.unpair.comp (Computable.snd.comp Computable.unpair)))))))

def leftCoordinate (n : ℕ) : ℕ :=
  Nat.pair (Nat.unpair n).1 (Nat.unpair (Nat.unpair (Nat.unpair n).2).2).1

def rightCoordinate (n : ℕ) : ℕ :=
  Nat.pair (Nat.unpair n).1 (Nat.unpair (Nat.unpair (Nat.unpair n).2).2).2

theorem leftCoordinate_computable : Computable leftCoordinate :=
  Primrec₂.natPair.to_comp.comp (Computable.fst.comp Computable.unpair)
    (Computable.fst.comp (Computable.unpair.comp
      (Computable.snd.comp (Computable.unpair.comp
        (Computable.snd.comp Computable.unpair)))))

theorem rightCoordinate_computable : Computable rightCoordinate :=
  Primrec₂.natPair.to_comp.comp (Computable.fst.comp Computable.unpair)
    (Computable.snd.comp (Computable.unpair.comp
      (Computable.snd.comp (Computable.unpair.comp
        (Computable.snd.comp Computable.unpair)))))

def V : Object where
  center := natCarrier
  left := natCarrier
  right := natCarrier
  leftMap := EnumerableCarriers.totalFromFunction leftCoordinate leftCoordinate_computable
    (fun _ _ => Set.mem_univ _)
  rightMap := EnumerableCarriers.totalFromFunction rightCoordinate rightCoordinate_computable
    (fun _ _ => Set.mem_univ _)
  left_total := EnumerableCarriers.totalFromFunction_total leftCoordinate leftCoordinate_computable
    (fun _ _ => Set.mem_univ _)
  right_total := EnumerableCarriers.totalFromFunction_total rightCoordinate rightCoordinate_computable
    (fun _ _ => Set.mem_univ _)

theorem mem_V_left (x y : ℕ) : y ∈ val V.leftMap x ↔ y=leftCoordinate x :=
  (EnumerableCarriers.mem_totalFromFunction leftCoordinate leftCoordinate_computable
    (fun _ _ => Set.mem_univ _) x y).trans (and_iff_right (Set.mem_univ x))

theorem mem_V_right (x y : ℕ) : y ∈ val V.rightMap x ↔ y=rightCoordinate x :=
  (EnumerableCarriers.mem_totalFromFunction rightCoordinate rightCoordinate_computable
    (fun _ _ => Set.mem_univ _) x y).trans (and_iff_right (Set.mem_univ x))

@[simp] theorem left_quad (k z a b : ℕ) : leftCoordinate (quadCode (k,z,a,b)) = Nat.pair k a := by
  simp [leftCoordinate, quadCode]

@[simp] theorem right_quad (k z a b : ℕ) : rightCoordinate (quadCode (k,z,a,b)) = Nat.pair k b := by
  simp [rightCoordinate, quadCode]

/-- These are the component values; no whole-space cosheaf value is used here. -/
def universalDiagram : Fork.Diagram := ⟨ℕ, ℕ, ℕ, leftCoordinate, rightCoordinate⟩

theorem universal_no_decidable_equality : ¬ Nonempty (Fork.EqualityDecision universalDiagram) := by
  rintro ⟨e⟩
  have he := e.leftMap_injective
    (a₁ := quadCode (0,0,0,0)) (a₂ := quadCode (0,1,0,0))
    (by simp [universalDiagram])
  have h : (0 : ℕ)=1 := by
    simpa only [Equiv.symm_apply_apply] using
      congrArg (fun n => (quadCode.symm n).2.1) he
  exact Nat.zero_ne_one h

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
