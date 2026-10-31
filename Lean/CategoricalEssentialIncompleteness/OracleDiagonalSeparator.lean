/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.OracleHalting

/-! # The actual even-output separator is nonrecursive and decidable in K -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation

open Nat.Partrec (Code)
open Encodable Denumerable

def ordinaryDiagonal (q : ℕ) : Part ℕ := ordinaryEval (Nat.unpair q).1 q
def A : Set ℕ := {q | ∃ z,z ∈ ordinaryDiagonal q ∧ z%2=0}

theorem ordinaryDiagonal_partrec : Partrec ordinaryDiagonal := ordinaryEval_partrec.comp
  (Computable.fst.comp Computable.unpair) Computable.id

theorem A_re : REPred (· ∈ A) := by
  have hp : ComputablePred (fun p : ℕ × ℕ => p.2%2=0) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (.const 2)) (.const 0)).computablePred
  exact ((partrecGraph ordinaryDiagonal_partrec).and hp.to_re).projection

def simulationCode (n : ℕ) : Code := .comp .zero (.comp (ofNat Code n) (.const n))

theorem simulationCode_computable : Computable simulationCode :=
  Code.primrec₂_comp.to_comp.comp (Computable.const Code.zero)
    (Code.primrec₂_comp.to_comp.comp (Computable.ofNat Code) Code.primrec_const.to_comp)

def K_reduction_A (n : ℕ) : ℕ := Nat.pair (encode (simulationCode n)) 0

theorem K_reduction_A_computable : Computable K_reduction_A :=
  Primrec₂.natPair.to_comp.comp (Computable.encode.comp simulationCode_computable) (Computable.const 0)

theorem ordinaryDiagonal_reduction (n : ℕ) :
    ordinaryDiagonal (K_reduction_A n)=(ordinaryEval n n).map (fun _ => 0) := by
  simp only [ordinaryDiagonal,K_reduction_A,Nat.unpair_pair,ordinaryEval,
    Denumerable.ofNat_encode,simulationCode,Code.eval,Code.eval_const,
    Part.bind_eq_bind,Part.bind_some,Part.bind_some_eq_map]
  change ((ofNat Code n).eval n).bind (fun _ => Part.some 0)=_
  exact Part.bind_some_eq_map _ _

theorem K_iff_reduction_A (n : ℕ) : n ∈ K ↔ K_reduction_A n ∈ A := by
  change (ordinaryEval n n).Dom ↔ ∃ z,z ∈ ordinaryDiagonal (K_reduction_A n) ∧ z%2=0
  rw [ordinaryDiagonal_reduction]
  constructor
  · intro h
    obtain ⟨z,hz⟩ := Part.dom_iff_mem.mp h
    exact ⟨0,(Part.mem_map_iff _).mpr ⟨z,hz,rfl⟩,rfl⟩
  · rintro ⟨z,hz,_⟩
    obtain ⟨w,hw,_⟩ := (Part.mem_map_iff _).mp hz
    exact hw.1

theorem A_not_recursive : ¬ ComputablePred (· ∈ A) := by
  intro h
  classical
  apply K_not_recursive
  have hc : ComputablePred (fun n => K_reduction_A n ∈ A) :=
    ⟨inferInstance,h.decide.comp K_reduction_A_computable⟩
  exact hc.of_eq (fun n => (K_iff_reduction_A n).symm)

theorem A_oracle_domains : FiniteOracleRE K (· ∈ A) ∧ FiniteOracleRE K (fun n => n ∉ A) :=
  K_decides_re A_re

theorem A_oracle_decidable : Nat.RecursiveIn (oracleSet K) (oracleFunction A) := by
  obtain ⟨h,hh,he⟩ := re_reduces_K A_re
  have hk : Nat.RecursiveIn (oracleSet K) (oracleFunction K) := .oracle _ (Set.mem_singleton _)
  refine (Nat.RecursiveIn.comp hk (recursiveIn_of_computable hh)).of_eq ?_
  intro n
  simp only [Part.bind_eq_bind,Part.bind_some,oracleFunction]
  congr 1
  classical
  simp only [answer,← he n]

end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation
