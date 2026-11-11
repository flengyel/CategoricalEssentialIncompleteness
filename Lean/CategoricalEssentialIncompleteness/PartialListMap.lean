/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Foundation.Vorspiel.Computability

/-! # Partial recursive maps on finite lists -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.PartialLists

open Nat.Partrec (Code)

def traverse (f : ℕ → Part ℕ) : List ℕ → Part (List ℕ)
  | [] => Part.some []
  | x::xs => (f x).bind (fun y => (traverse f xs).map (List.cons y))

@[simp] theorem mem_traverse (f : ℕ → Part ℕ) (xs ys : List ℕ) :
    ys ∈ traverse f xs ↔ List.Forall₂ (fun x y => y ∈ f x) xs ys := by
  induction xs generalizing ys with
  | nil => simp [traverse,Part.mem_some_iff,List.forall₂_nil_left_iff]
  | cons x xs ih =>
    cases ys with
    | nil => simp [traverse,Part.mem_bind_iff,Part.mem_map_iff]
    | cons y ys => simp [traverse,Part.mem_bind_iff,Part.mem_map_iff,ih]

def bounded (c : Code) (t : ℕ) : List ℕ → Option (List ℕ)
  | [] => some []
  | x::xs => (c.evaln t x).bind (fun y => (bounded c t xs).map (List.cons y))

theorem bounded_primrec (c : Code) : Primrec₂ (bounded c) := by
  have hc : Primrec (fun q : (ℕ × List ℕ) × ℕ × List ℕ × Option (List ℕ) =>
      c.evaln q.1.1 q.2.1) :=
    Code.primrec_evaln.comp (Primrec.pair (Primrec.pair
      (Primrec.fst.comp Primrec.fst) (Primrec.const c)) (Primrec.fst.comp Primrec.snd))
  have hh : Primrec (fun q : (ℕ × List ℕ) × ℕ × List ℕ × Option (List ℕ) =>
      (c.evaln q.1.1 q.2.1).bind (fun y => q.2.2.2.map (List.cons y))) :=
    Primrec.option_bind hc (Primrec.option_map
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂
  have hb : Primrec (fun q : ℕ × List ℕ => bounded c q.1 q.2) := by
    apply (Primrec.list_rec Primrec.snd (Primrec.const (some [])) hh.to₂).of_eq
    intro q
    rcases q with ⟨t,xs⟩
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simpa only [bounded] using congrArg
        (fun z : Option (List ℕ) => (c.evaln t x).bind (fun y => z.map (List.cons y))) ih
  exact hb.to₂

theorem mem_bounded (c : Code) (t : ℕ) (xs ys : List ℕ) :
    ys ∈ bounded c t xs ↔ List.Forall₂ (fun x y => y ∈ c.evaln t x) xs ys := by
  induction xs generalizing ys with
  | nil => simp [bounded,List.forall₂_nil_left_iff]
  | cons x xs ih =>
    cases ys with
    | nil => simp [bounded,Option.bind_eq_some_iff,Option.map_eq_some_iff]
    | cons y ys =>
      simp only [Option.mem_def] at ih
      simp [bounded,Option.bind_eq_some_iff,Option.map_eq_some_iff,Option.mem_def,ih]

theorem bounded_mono (c : Code) {s t : ℕ} (hst : s≤t) {xs ys : List ℕ}
    (h : ys ∈ bounded c s xs) : ys ∈ bounded c t xs := by
  rw [mem_bounded] at h ⊢
  exact h.imp (fun _ _ hxy => Code.evaln_mono hst hxy)

theorem traverse_eq_search (c : Code) (xs : List ℕ) :
    traverse c.eval xs=Nat.rfindOpt (fun t => bounded c t xs) := by
  apply Part.ext
  intro ys
  rw [mem_traverse,Nat.rfindOpt_mono (fun {a m n} h hy => bounded_mono c h hy)]
  constructor
  · intro h
    induction h with
    | nil => exact ⟨0,rfl⟩
    | @cons x y xs ys hxy hxs ih =>
      obtain ⟨s,hs⟩ := Code.evaln_complete.mp hxy
      obtain ⟨t,ht⟩ := ih
      rw [mem_bounded] at ht
      refine ⟨max s t,(mem_bounded _ _ _ _).mpr ?_⟩
      exact List.Forall₂.cons (Code.evaln_mono (le_max_left _ _) hs)
        (ht.imp (fun _ _ h => Code.evaln_mono (le_max_right _ _) h))
  · rintro ⟨t,ht⟩
    rw [mem_bounded] at ht
    exact ht.imp (fun _ _ h => Code.evaln_complete.mpr ⟨t,h⟩)

theorem traverse_partrec {f : ℕ → Part ℕ} (hf : Partrec f) : Partrec (traverse f) := by
  obtain ⟨c,hc⟩ := Code.exists_code.mp (Partrec.nat_iff.mp hf)
  subst f
  exact (Partrec.rfindOpt (((bounded_primrec c).to_comp.comp
    Computable.snd Computable.fst).to₂)).of_eq
    (fun xs => (traverse_eq_search c xs).symm)

end CategoricalEssentialIncompleteness.LocalConnectedness.PartialLists
