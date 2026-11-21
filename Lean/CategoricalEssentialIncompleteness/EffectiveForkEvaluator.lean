/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EffectiveForkEncoding
public import Mathlib.Computability.PartrecCode

/-! # The three checked computations defining the fork evaluator -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory Encodable Denumerable
open Nat.Partrec (Code)
open FailureOfComposition.Kleene (eval)

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open EnumerableCarriers (Carrier val)

theorem eval_with_partrec {p x : ℕ → ℕ} (hp : Computable p) (hx : Computable x) :
    Partrec (fun n => eval (p n) (x n)) :=
  Code.eval_part.comp ((Computable.ofNat Code).comp hp) hx

def endpointEval (n : ℕ) : Part ℕ := eval (Nat.unpair (Nat.unpair n).1).2 (Nat.unpair n).2

theorem endpointEval_partrec : Partrec endpointEval :=
  eval_with_partrec (Computable.snd.comp (Computable.unpair.comp
    (Computable.fst.comp Computable.unpair))) (Computable.snd.comp Computable.unpair)

def centralEval (n : ℕ) : Part ℕ :=
  eval (quadCode.symm (Nat.unpair n).1).2.1 (Nat.unpair n).2
def leftEval (n : ℕ) : Part ℕ :=
  eval (quadCode.symm (Nat.unpair n).1).2.2.1 (leftCoordinate (Nat.unpair n).2)
def rightEval (n : ℕ) : Part ℕ :=
  eval (quadCode.symm (Nat.unpair n).1).2.2.2 (rightCoordinate (Nat.unpair n).2)

theorem centralEval_partrec : Partrec centralEval :=
  eval_with_partrec (Computable.fst.comp (Computable.snd.comp
    (quadDecode_computable.comp (Computable.fst.comp Computable.unpair))))
    (Computable.snd.comp Computable.unpair)
theorem leftEval_partrec : Partrec leftEval :=
  eval_with_partrec (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
    (quadDecode_computable.comp (Computable.fst.comp Computable.unpair)))))
    (leftCoordinate_computable.comp (Computable.snd.comp Computable.unpair))
theorem rightEval_partrec : Partrec rightEval :=
  eval_with_partrec (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
    (quadDecode_computable.comp (Computable.fst.comp Computable.unpair)))))
    (rightCoordinate_computable.comp (Computable.snd.comp Computable.unpair))

def checkedOutput (q : ℕ × ℕ × ℕ) : Part ℕ :=
  if q.2.1=leftCoordinate q.1 ∧ q.2.2=rightCoordinate q.1 then Part.some q.1 else Part.none

theorem checkedOutput_partrec : Partrec checkedOutput := by
  have hp : ComputablePred (fun q : ℕ × ℕ × ℕ =>
      q.2.1=leftCoordinate q.1 ∧ q.2.2=rightCoordinate q.1) :=
    ((Primrec.eq.decide.to_comp.comp (Computable.fst.comp Computable.snd)
      (leftCoordinate_computable.comp Computable.fst)).computablePred).and
      ((Primrec.eq.decide.to_comp.comp (Computable.snd.comp Computable.snd)
        (rightCoordinate_computable.comp Computable.fst)).computablePred)
  apply (Partrec.cond hp.decide Computable.fst.partrec Partrec.none).of_eq
  intro q
  by_cases h : q.2.1=leftCoordinate q.1 ∧ q.2.2=rightCoordinate q.1 <;>
    simp [checkedOutput, h]

@[simp] theorem mem_checkedOutput (c a b y : ℕ) :
    y ∈ checkedOutput (c,a,b) ↔ a=leftCoordinate c ∧ b=rightCoordinate c ∧ y=c := by
  by_cases h : a=leftCoordinate c ∧ b=rightCoordinate c <;>
    simp [checkedOutput, h, and_assoc] <;> aesop

def centerEval (n : ℕ) : Part ℕ :=
  (centralEval n).bind fun c => (leftEval n).bind fun a => (rightEval n).bind
    (fun b => checkedOutput (c,a,b))

theorem centerEval_partrec : Partrec centerEval :=
  centralEval_partrec.bind
    ((leftEval_partrec.comp Computable.fst).bind
      ((rightEval_partrec.comp (Computable.fst.comp Computable.fst)).bind
        (checkedOutput_partrec.comp (Computable.pair
          (Computable.snd.comp (Computable.fst.comp Computable.fst))
          (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd))).to₂).to₂).to₂

theorem mem_centerEval (n y : ℕ) : y ∈ centerEval n ↔
    y ∈ centralEval n ∧ leftCoordinate y ∈ leftEval n ∧ rightCoordinate y ∈ rightEval n := by
  simp only [centerEval, Part.mem_bind_iff, mem_checkedOutput]
  aesop

theorem endpoint_left (p x : ℕ) :
    endpointEval (Nat.pair (leftCoordinate p) (leftCoordinate x)) = leftEval (Nat.pair p x) := by
  simp [endpointEval, leftEval, leftCoordinate, quadCode]

theorem endpoint_right (p x : ℕ) :
    endpointEval (Nat.pair (rightCoordinate p) (rightCoordinate x)) = rightEval (Nat.pair p x) := by
  simp [endpointEval, rightEval, rightCoordinate, quadCode]

def endpointEvaluator : EnumerableCarriers.product natCarrier natCarrier ⟶ natCarrier :=
  EnumerableCarriers.arrow endpointEval endpointEval_partrec
    (fun _ _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩) (fun _ _ _ => Set.mem_univ _)

def centerEvaluator : EnumerableCarriers.product natCarrier natCarrier ⟶ natCarrier :=
  EnumerableCarriers.arrow centerEval centerEval_partrec
    (fun _ _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩) (fun _ _ _ => Set.mem_univ _)

theorem centerEvaluator_left : Respects (product V V).leftMap V.leftMap
    centerEvaluator endpointEvaluator := by
  intro n y u v hny hnu hyv
  have hh := (mem_centerEval n y).mp hny
  have hu := (EnumerableCarriers.mem_partialProdMap_iff V.leftMap V.leftMap n u).mp hnu
  obtain ⟨hp, hx⟩ := hu
  have hp' := (mem_V_left _ _).mp hp
  have hx' := (mem_V_left _ _).mp hx
  have hu' : u=Nat.pair (leftCoordinate (Nat.unpair n).1)
      (leftCoordinate (Nat.unpair n).2) := by
    rw [← hp', ← hx', Nat.pair_unpair]
  have hv := (mem_V_left y v).mp hyv
  change v ∈ endpointEval u
  rw [hu', endpoint_left, Nat.pair_unpair, hv]
  exact hh.2.1

theorem centerEvaluator_right : Respects (product V V).rightMap V.rightMap
    centerEvaluator endpointEvaluator := by
  intro n y u v hny hnu hyv
  have hh := (mem_centerEval n y).mp hny
  have hu := (EnumerableCarriers.mem_partialProdMap_iff V.rightMap V.rightMap n u).mp hnu
  obtain ⟨hp, hx⟩ := hu
  have hp' := (mem_V_right _ _).mp hp
  have hx' := (mem_V_right _ _).mp hx
  have hu' : u=Nat.pair (rightCoordinate (Nat.unpair n).1)
      (rightCoordinate (Nat.unpair n).2) := by
    rw [← hp', ← hx', Nat.pair_unpair]
  have hv := (mem_V_right y v).mp hyv
  change v ∈ endpointEval u
  rw [hu', endpoint_right, Nat.pair_unpair, hv]
  exact hh.2.2

/-- The endpoint computations and the central compatibility check have their domains. -/
def tau : product V V ⟶ V :=
  ⟨centerEvaluator, endpointEvaluator, endpointEvaluator,
    centerEvaluator_left, centerEvaluator_right⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
