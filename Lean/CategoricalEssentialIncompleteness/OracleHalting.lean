/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.OracleRestrictedCategory
import Mathlib.Computability.Halting

/-! # The actual diagonal halting oracle decides every ordinary c.e. predicate -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation

open Nat.Partrec (Code)
open Encodable Denumerable

def ordinaryEval (e x : ℕ) : Part ℕ := Code.eval (ofNat Code e) x

theorem ordinaryEval_partrec : Partrec₂ ordinaryEval := Code.eval_part.comp
  ((Computable.ofNat Code).comp Computable.fst) Computable.snd

def K : Set ℕ := {e | (ordinaryEval e e).Dom}

theorem K_re : REPred (· ∈ K) :=
  (ordinaryEval_partrec.comp Computable.id Computable.id).dom_re

theorem K_not_recursive : ¬ ComputablePred (· ∈ K) := by
  intro hK
  classical
  let f : ℕ → Part ℕ := fun n => if n ∈ K then Part.none else Part.some 0
  have hf : Partrec f := by
    simpa only [Bool.cond_decide] using
      Partrec.cond hK.decide Partrec.none (Partrec.const' (Part.some 0))
  obtain ⟨c,hc⟩ := Code.exists_code.mp (Partrec.nat_iff.mp hf)
  let q := encode c
  have he : q ∈ K ↔ (f q).Dom := by
    change (Code.eval (ofNat Code (encode c)) q).Dom ↔ (f q).Dom
    rw [Denumerable.ofNat_encode,hc]
  by_cases hq : q ∈ K
  · have h := he.mp hq
    simpa only [f,if_pos hq,Part.none] using h
  · apply hq
    apply he.mpr
    simp only [f,if_neg hq,Part.some_dom]

def haltIndex (c : Code) (n : ℕ) : ℕ := encode (.comp c (.const n) : Code)

theorem haltIndex_computable (c : Code) : Computable (haltIndex c) :=
  Computable.encode.comp (Code.primrec₂_comp.to_comp.comp (Computable.const c)
    Code.primrec_const.to_comp)

theorem haltIndex_mem (c : Code) (n : ℕ) : haltIndex c n ∈ K ↔ (c.eval n).Dom := by
  change (Code.eval (ofNat Code (encode (Code.comp c (Code.const n)))) (haltIndex c n)).Dom ↔ _
  simp only [Denumerable.ofNat_encode,Code.eval,Code.eval_const,Part.bind_eq_bind,Part.bind_some]

theorem re_reduces_K {p : ℕ → Prop} (hp : REPred p) :
    ∃ h : ℕ → ℕ,Computable h ∧ ∀ n,p n ↔ h n ∈ K := by
  obtain ⟨c,hc⟩ := predicate_code hp
  exact ⟨haltIndex c,haltIndex_computable c,fun n => (hc n).symm.trans (haltIndex_mem c n).symm⟩

theorem oracle_membership (S : Set ℕ) : FiniteOracleRE S (· ∈ S) := by
  have hq : ComputablePred (fun p : ℕ × List ℕ => p.2[p.1]?=some 1) :=
    (Primrec.eq.comp (Primrec.list_getElem?.comp Primrec.snd Primrec.fst)
      (Primrec.const (some 1))).computablePred
  apply (finiteOracleRE_of_prefix S hq.to_re).of_eq
  intro x
  constructor
  · rintro ⟨n,hn⟩
    have hx : x<n := by simpa only [prefix_length] using (List.getElem?_eq_some_iff.mp hn).1
    rw [oraclePrefix,List.getElem?_map,List.getElem?_range hx,Option.map_some] at hn
    have ha := Option.some.inj hn
    simpa [answer] using ha
  · intro hx
    exact ⟨x+1,by simp [oraclePrefix,List.getElem?_map,List.getElem?_range (by omega : x<x+1),answer,hx]⟩

theorem oracle_complement (S : Set ℕ) : FiniteOracleRE S (fun n => n ∉ S) := by
  have hq : ComputablePred (fun p : ℕ × List ℕ => p.2[p.1]?=some 0) :=
    (Primrec.eq.comp (Primrec.list_getElem?.comp Primrec.snd Primrec.fst)
      (Primrec.const (some 0))).computablePred
  apply (finiteOracleRE_of_prefix S hq.to_re).of_eq
  intro x
  constructor
  · rintro ⟨n,hn⟩
    have hx : x<n := by simpa only [prefix_length] using (List.getElem?_eq_some_iff.mp hn).1
    rw [oraclePrefix,List.getElem?_map,List.getElem?_range hx,Option.map_some] at hn
    have ha := Option.some.inj hn
    simpa [answer] using ha
  · intro hx
    exact ⟨x+1,by simp [oraclePrefix,List.getElem?_map,List.getElem?_range (by omega : x<x+1),answer,hx]⟩

/-- In particular every ordinary c.e. set and its complement are c.e. in
the actual diagonal halting oracle. -/
theorem K_decides_re {p : ℕ → Prop} (hp : REPred p) :
    FiniteOracleRE K p ∧ FiniteOracleRE K (fun n => ¬p n) := by
  obtain ⟨h,hh,he⟩ := re_reduces_K hp
  exact ⟨((oracle_membership K).comp hh).of_eq (fun n => (he n).symm),
    ((oracle_complement K).comp hh).of_eq (fun n => not_congr (he n).symm)⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation
