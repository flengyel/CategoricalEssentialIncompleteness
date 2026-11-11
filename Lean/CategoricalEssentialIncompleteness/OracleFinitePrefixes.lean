/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Foundation.Vorspiel.Computability
public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.RecursiveIn
public import Mathlib.Data.List.Range

/-! # Finite oracle prefixes and effective relative semidecision certificates

This is an explicit finite-query presentation. The comparison with oracle
recursive functions is developed separately before it is used for Appendix C.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation

def answer (S : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact if n ∈ S then 1 else 0

def oraclePrefix (S : Set ℕ) (n : ℕ) : List ℕ := (List.range n).map (answer S)

@[simp] theorem prefix_length (S : Set ℕ) (n : ℕ) : (oraclePrefix S n).length=n := by
  simp [oraclePrefix]

theorem take_prefix (S : Set ℕ) (n k : ℕ) : (oraclePrefix S n).take k=oraclePrefix S (min k n) := by
  simp [oraclePrefix,← List.map_take,List.take_range]

theorem prefix_le (S : Set ℕ) {n m : ℕ} (h : n ≤ m) : oraclePrefix S n <+: oraclePrefix S m := by
  refine ⟨(oraclePrefix S m).drop n,?_⟩
  rw [← show (oraclePrefix S m).take n=oraclePrefix S n by rw [take_prefix,Nat.min_eq_left h]]
  exact List.take_append_drop n (oraclePrefix S m)

def PrefixMonotone {α : Type} (Q : α × List ℕ → Prop) : Prop :=
  ∀ x l l',l <+: l' → Q (x,l) → Q (x,l')

def FiniteOracleRE {α : Type} [Primcodable α] (S : Set ℕ) (p : α → Prop) : Prop :=
  ∃ Q : α × List ℕ → Prop,REPred Q ∧ PrefixMonotone Q ∧
    ∀ x,p x ↔ ∃ n,Q (x,oraclePrefix S n)

namespace FiniteOracleRE

variable {α β : Type} [Primcodable α] [Primcodable β]
  {S : Set ℕ} {p q : α → Prop}

theorem of_eq (hp : FiniteOracleRE S p) (h : ∀ x, p x ↔ q x) : FiniteOracleRE S q := by
  obtain ⟨Q,hQ,hM,hP⟩ := hp
  exact ⟨Q,hQ,hM,fun x => (h x).symm.trans (hP x)⟩

theorem of_re (hp : REPred p) : FiniteOracleRE S p :=
  ⟨fun q => p q.1,REPred.comp Computable.fst hp,
    fun _ _ _ _ h => h,fun _ => ⟨fun h => ⟨0,h⟩,fun ⟨_,h⟩ => h⟩⟩

theorem comp {f : β → α} (hf : Computable f) (hp : FiniteOracleRE S p) :
    FiniteOracleRE S (fun x => p (f x)) := by
  obtain ⟨Q,hQ,hM,hP⟩ := hp
  exact ⟨fun q => Q (f q.1,q.2),
    REPred.comp (Computable.pair (hf.comp Computable.fst) Computable.snd) hQ,
    fun x l l' h => hM (f x) l l' h,fun x => hP (f x)⟩

theorem and (hp : FiniteOracleRE S p) (hq : FiniteOracleRE S q) :
    FiniteOracleRE S (fun x => p x ∧ q x) := by
  obtain ⟨P,hP,hMP,hp⟩ := hp
  obtain ⟨Q,hQ,hMQ,hq⟩ := hq
  refine ⟨fun x => P x ∧ Q x,hP.and hQ,
    fun x l l' h ⟨hp,hq⟩ => ⟨hMP x l l' h hp,hMQ x l l' h hq⟩,?_⟩
  intro x
  change (p x ∧ q x) ↔ ∃ n,P (x,oraclePrefix S n) ∧ Q (x,oraclePrefix S n)
  rw [hp,hq]
  constructor
  · rintro ⟨⟨n,hn⟩,⟨m,hm⟩⟩
    exact ⟨max n m,hMP x _ _ (prefix_le S (le_max_left _ _)) hn,
      hMQ x _ _ (prefix_le S (le_max_right _ _)) hm⟩
  · rintro ⟨n,hp,hq⟩
    exact ⟨⟨n,hp⟩,⟨n,hq⟩⟩

theorem or (hp : FiniteOracleRE S p) (hq : FiniteOracleRE S q) :
    FiniteOracleRE S (fun x => p x ∨ q x) := by
  obtain ⟨P,hP,hMP,hp⟩ := hp
  obtain ⟨Q,hQ,hMQ,hq⟩ := hq
  refine ⟨fun x => P x ∨ Q x,hP.or hQ,
    fun x l l' h => Or.imp (hMP x l l' h) (hMQ x l l' h),?_⟩
  intro x
  simp only [hp,hq,exists_or]

theorem projection {p : α × β → Prop} (hp : FiniteOracleRE S p) :
    FiniteOracleRE S (fun x => ∃ y,p (x,y)) := by
  obtain ⟨Q,hQ,hM,hp⟩ := hp
  have hQ' : REPred (fun q : (α × List ℕ) × β => Q ((q.1.1,q.2),q.1.2)) :=
    REPred.comp (Computable.pair
      (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
      (Computable.snd.comp Computable.fst)) hQ
  refine ⟨fun q => ∃ y,Q ((q.1,y),q.2),hQ'.projection,?_,?_⟩
  · rintro x l l' h ⟨y,hy⟩
    exact ⟨y,hM (x,y) l l' h hy⟩
  · intro x
    simp only [hp]
    exact exists_comm

end FiniteOracleRE

/-- Closing an ordinary semidecision predicate under extension of its finite
oracle input does not change which canonical prefixes eventually satisfy it. -/
def monotonize {α : Type} (Q : α × List ℕ → Prop) (q : α × List ℕ) : Prop :=
  ∃ k,k ≤ q.2.length ∧ Q (q.1,q.2.take k)

theorem monotonize_re {α : Type} [Primcodable α] {Q : α × List ℕ → Prop}
    (hQ : REPred Q) : REPred (monotonize Q) := by
  have ht : Computable (fun q : (α × List ℕ) × ℕ => (q.1.1,q.1.2.take q.2)) :=
    Computable.pair (Computable.fst.comp Computable.fst)
      (Primrec.list_take.to_comp.comp Computable.snd (Computable.snd.comp Computable.fst))
  have hb : ComputablePred (fun q : (α × List ℕ) × ℕ => q.2 ≤ q.1.2.length) :=
    (Primrec.nat_le.comp Primrec.snd
      (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))).computablePred
  exact (hb.to_re.and (REPred.comp ht hQ)).projection

theorem monotonize_monotone {α : Type} (Q : α × List ℕ → Prop) :
    PrefixMonotone (monotonize Q) := by
  rintro x l l' ⟨t,rfl⟩ ⟨k,hk,hQ⟩
  change k ≤ l.length at hk
  refine ⟨k,by simp only [List.length_append]; omega,?_⟩
  simpa only [List.take_append_of_le_length hk] using hQ

theorem monotonize_prefix_iff {α : Type} (S : Set ℕ) (Q : α × List ℕ → Prop) (x : α) :
    (∃ n,monotonize Q (x,oraclePrefix S n)) ↔ ∃ n,Q (x,oraclePrefix S n) := by
  constructor
  · rintro ⟨n,k,hk,hQ⟩
    rw [take_prefix] at hQ
    exact ⟨min k n,hQ⟩
  · rintro ⟨n,hQ⟩
    exact ⟨n,n,by simp,by simpa only [take_prefix,Nat.min_self] using hQ⟩

theorem finiteOracleRE_of_prefix {α : Type} [Primcodable α]
    (S : Set ℕ) {Q : α × List ℕ → Prop} (hQ : REPred Q) :
    FiniteOracleRE S (fun x => ∃ n,Q (x,oraclePrefix S n)) :=
  ⟨monotonize Q,monotonize_re hQ,monotonize_monotone Q,
    fun x => (monotonize_prefix_iff S Q x).symm⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation
