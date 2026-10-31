/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.OracleApproximationRecursion

/-! # Finite oracle approximations commute with partial minimization -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation

theorem MonotoneValues.map_mem {F : List ℕ × ℕ → Part ℕ} (hF : MonotoneValues F)
    {β : Type} (v : ℕ → β) (l l' : List ℕ) (hl : l <+: l') (x : ℕ) (y : β) :
    y ∈ (F (l,x)).map v → y ∈ (F (l',x)).map v := by
  intro hy
  obtain ⟨z,hz,he⟩ := (Part.mem_map_iff _).mp hy
  exact (Part.mem_map_iff _).mpr ⟨z,hF l l' hl x z hz,he⟩

theorem Represents.map_mem {S : Set ℕ} {F : List ℕ × ℕ → Part ℕ} {f : ℕ → Part ℕ}
    (hF : Represents S F f) {β : Type} (v : ℕ → β) (x : ℕ) (y : β) :
    y ∈ (f x).map v ↔ ∃ n,y ∈ (F (oraclePrefix S n,x)).map v := by
  constructor
  · intro hy
    obtain ⟨z,hz,he⟩ := (Part.mem_map_iff _).mp hy
    obtain ⟨n,hn⟩ := (hF x z).mp hz
    exact ⟨n,(Part.mem_map_iff _).mpr ⟨z,hn,he⟩⟩
  · rintro ⟨n,hy⟩
    obtain ⟨z,hz,he⟩ := (Part.mem_map_iff _).mp hy
    exact (Part.mem_map_iff _).mpr ⟨z,(hF x z).mpr ⟨n,hz⟩,he⟩

theorem finite_bound {P : ℕ → ℕ → Prop}
    (hM : ∀ i k k',k ≤ k' → P i k → P i k') (n : ℕ)
    (h : ∀ i,i ≤ n → ∃ k,P i k) : ∃ k,∀ i,i ≤ n → P i k := by
  induction n with
  | zero =>
    obtain ⟨k,hk⟩ := h 0 le_rfl
    exact ⟨k,fun i hi => (Nat.eq_zero_of_le_zero hi) ▸ hk⟩
  | succ n ih =>
    obtain ⟨k,hk⟩ := ih (fun i hi => h i (hi.trans (Nat.le_succ n)))
    obtain ⟨m,hm⟩ := h (n+1) le_rfl
    refine ⟨max k m,fun i hi => ?_⟩
    by_cases hin : i ≤ n
    · exact hM i k _ (le_max_left _ _) (hk i hin)
    · have he : i=n+1 := by omega
      subst i
      exact hM _ m _ (le_max_right _ _) hm

def finiteSearch (F : List ℕ × ℕ → Part ℕ) (l : List ℕ) (a : ℕ) : Part ℕ :=
  Nat.rfind (fun n => (F (l,Nat.pair a n)).map (fun m => decide (m=0)))

theorem finiteSearch_partrec {F : List ℕ × ℕ → Part ℕ} (hF : Partrec F) :
    Partrec (fun p : List ℕ × ℕ => finiteSearch F p.1 p.2) := by
  have hc : Computable (fun m : ℕ => decide (m=0)) :=
    (Primrec.eq.comp Primrec.id (Primrec.const 0)).computablePred.decide
  have h := (hF.comp (Computable.pair (Computable.fst.comp Computable.fst)
    (Primrec₂.natPair.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd))).map
    (hc.comp Computable.snd).to₂
  exact Partrec.rfind h.to₂

theorem finiteSearch_monotone {F : List ℕ × ℕ → Part ℕ} (hF : MonotoneValues F) :
    MonotoneValues (fun p => finiteSearch F p.1 p.2) := by
  intro l l' hl x y hy
  obtain ⟨ht,hmin⟩ := Nat.mem_rfind.mp hy
  exact Nat.mem_rfind.mpr
    ⟨hF.map_mem _ l l' hl _ true ht,
      fun {m} hm => hF.map_mem _ l l' hl _ false (hmin hm)⟩

theorem finiteSearch_represents {S : Set ℕ} {F : List ℕ × ℕ → Part ℕ} {f : ℕ → Part ℕ}
    (hM : MonotoneValues F) (hf : Represents S F f) :
    Represents S (fun p => finiteSearch F p.1 p.2)
      (fun a => Nat.rfind (fun n => (f (Nat.pair a n)).map (fun m => decide (m=0)))) := by
  intro a n
  constructor
  · intro hn
    obtain ⟨ht,hmin⟩ := Nat.mem_rfind.mp hn
    let P (i k : ℕ) := (if i=n then true else false) ∈
      (F (oraclePrefix S k,Nat.pair a i)).map (fun m => decide (m=0))
    have hm : ∀ i k k',k ≤ k' → P i k → P i k' := by
      intro i k k' hkk'
      exact hM.map_mem _ _ _ (prefix_le S hkk') _ _
    have hex : ∀ i,i ≤ n → ∃ k,P i k := by
      intro i hi
      by_cases he : i=n
      · subst i
        simpa [P] using (hf.map_mem _ _ true).mp ht
      · have hil : i<n := by omega
        simpa only [P,if_neg he] using (hf.map_mem _ _ false).mp (hmin hil)
    obtain ⟨k,hk⟩ := finite_bound hm n hex
    refine ⟨k,Nat.mem_rfind.mpr ⟨?_,?_⟩⟩
    · simpa [P] using hk n le_rfl
    · intro m hm
      simpa only [P,if_neg (by omega : m≠n)] using hk m (Nat.le_of_lt hm)
  · rintro ⟨k,hk⟩
    obtain ⟨ht,hmin⟩ := Nat.mem_rfind.mp hk
    exact Nat.mem_rfind.mpr ⟨(hf.map_mem _ _ true).mpr ⟨k,ht⟩,
      fun {m} hm => (hf.map_mem _ _ false).mpr ⟨k,hmin hm⟩⟩

theorem HasApproximation.rfind {S : Set ℕ} {f : ℕ → Part ℕ}
    (hf : HasApproximation S f) : HasApproximation S
      (fun a => Nat.rfind (fun n => (f (Nat.pair a n)).map (fun m => decide (m=0)))) := by
  obtain ⟨F,hF,hM,hf⟩ := hf
  exact ⟨_,finiteSearch_partrec hF,finiteSearch_monotone hM,finiteSearch_represents hM hf⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation
