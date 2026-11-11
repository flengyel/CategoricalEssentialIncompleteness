/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.PartialListMap

/-! # Finite multiplication with partial recursive multiplication programs -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.PartialLists

open Nat.Partrec (Code)

def foldl (mu : ℕ × ℕ → Part ℕ) (a : ℕ) : List ℕ → Part ℕ
  | [] => Part.some a
  | x::xs => (mu (a,x)).bind (fun b => foldl mu b xs)

def boundedFold (c : Code) (t : ℕ) (a : ℕ) : List ℕ → Option ℕ
  | [] => some a
  | x::xs => (c.evaln t (Nat.pair a x)).bind (fun b => boundedFold c t b xs)

theorem boundedFold_eq_foldl (c : Code) (t a : ℕ) (xs : List ℕ) :
    boundedFold c t a xs=xs.foldl (fun v x => v.bind (fun a => c.evaln t (Nat.pair a x)))
      (some a) := by
  have hn : ∀ l : List ℕ,l.foldl
      (fun v x => v.bind (fun a => c.evaln t (Nat.pair a x))) none=none := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih => exact ih
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [boundedFold,List.foldl_cons]
    cases h : c.evaln t (Nat.pair a x) with
    | none =>
      simp only [Option.bind_none,Option.bind_some,h,hn]
    | some b => simpa only [Option.bind_some,h] using ih b

theorem boundedFold_primrec (c : Code) :
    Primrec (fun p : ℕ × ℕ × List ℕ => boundedFold c p.1 p.2.1 p.2.2) := by
  have hs : Primrec (fun p : (ℕ × ℕ × List ℕ) × Option ℕ × ℕ =>
      p.2.1.bind (fun a => c.evaln p.1.1 (Nat.pair a p.2.2))) :=
    Primrec.option_bind (Primrec.fst.comp Primrec.snd)
      (Code.primrec_evaln.comp (Primrec.pair
        (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const c))
        (Primrec₂.natPair.comp Primrec.snd
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))).to₂
  apply (Primrec.list_foldl (Primrec.snd.comp Primrec.snd)
    (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd)) hs.to₂).of_eq
  intro p
  exact (boundedFold_eq_foldl c p.1 p.2.1 p.2.2).symm

theorem boundedFold_mono (c : Code) {s t : ℕ} (hst : s≤t)
    {a y : ℕ} {xs : List ℕ} (h : y ∈ boundedFold c s a xs) :
    y ∈ boundedFold c t a xs := by
  induction xs generalizing a with
  | nil => exact h
  | cons x xs ih =>
    obtain ⟨b,hb,hy⟩ := Option.bind_eq_some_iff.mp h
    exact Option.bind_eq_some_iff.mpr ⟨b,Code.evaln_mono hst hb,ih hy⟩

theorem foldl_eq_search (c : Code) (a : ℕ) (xs : List ℕ) :
    foldl (fun p => c.eval (Nat.pair p.1 p.2)) a xs=
      Nat.rfindOpt (fun t => boundedFold c t a xs) := by
  apply Part.ext
  intro y
  rw [Nat.rfindOpt_mono (fun {y s t} h hy => boundedFold_mono c h hy)]
  constructor
  · intro h
    induction xs generalizing a with
    | nil =>
      have hy : y=a := Part.mem_some_iff.mp h
      subst y
      exact ⟨0,rfl⟩
    | cons x xs ih =>
      obtain ⟨b,hb,hy⟩ := Part.mem_bind_iff.mp h
      obtain ⟨s,hs⟩ := Code.evaln_complete.mp hb
      obtain ⟨t,ht⟩ := ih b hy
      exact ⟨max s t,Option.bind_eq_some_iff.mpr
        ⟨b,Code.evaln_mono (le_max_left _ _) hs,
          boundedFold_mono c (le_max_right _ _) ht⟩⟩
  · rintro ⟨t,ht⟩
    induction xs generalizing a with
    | nil =>
      have hy : a=y := Option.some.inj ht
      subst y
      exact Part.mem_some a
    | cons x xs ih =>
      obtain ⟨b,hb,hy⟩ := Option.bind_eq_some_iff.mp ht
      exact Part.mem_bind_iff.mpr ⟨b,Code.evaln_complete.mpr ⟨t,hb⟩,ih b hy⟩

theorem foldl_partrec {mu : ℕ × ℕ → Part ℕ} (hmu : Partrec mu) :
    Partrec (fun p : ℕ × List ℕ => foldl mu p.1 p.2) := by
  obtain ⟨c,hc⟩ := Code.exists_code.mp (Partrec.nat_iff.mp (hmu.comp Computable.unpair))
  have he : mu=fun p => c.eval (Nat.pair p.1 p.2) := by
    funext p
    have h := congrFun hc (Nat.pair p.1 p.2)
    simpa only [Nat.unpair_pair] using h.symm
  rw [he]
  have hb : Computable (fun p : (ℕ × List ℕ) × ℕ => boundedFold c p.2 p.1.1 p.1.2) :=
    (boundedFold_primrec c).to_comp.comp (Computable.pair Computable.snd Computable.fst)
  exact (Partrec.rfindOpt hb.to₂).of_eq (fun p => (foldl_eq_search c p.1 p.2).symm)

theorem foldl_append (mu : ℕ × ℕ → Part ℕ) (a : ℕ) (xs ys : List ℕ) :
    foldl mu a (xs++ys)=(foldl mu a xs).bind (fun b => foldl mu b ys) := by
  induction xs generalizing a with
  | nil => simp [foldl]
  | cons x xs ih => simp only [List.cons_append,foldl,ih,Part.bind_assoc]

end CategoricalEssentialIncompleteness.LocalConnectedness.PartialLists
