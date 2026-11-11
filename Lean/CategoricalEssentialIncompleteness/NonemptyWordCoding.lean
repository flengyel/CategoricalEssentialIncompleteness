/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Foundation.Vorspiel.Computability

/-! # Uniform recursive tuple bijections and nonempty-word coding -/

@[expose] public section

noncomputable section
open Function

namespace CategoricalEssentialIncompleteness.LocalConnectedness.WordCoding

def tail (n : ℕ) : ℕ := (Nat.unpair n).2

/-- The final coordinate is retained without an extra pairing with zero. -/
def unpack (n a : ℕ) : List ℕ :=
  (List.range n).map (fun i => (Nat.unpair (tail^[i] a)).1) ++ [tail^[n] a]

@[simp] theorem unpack_zero (a : ℕ) : unpack 0 a=[a] := rfl

theorem unpack_succ (n a : ℕ) :
    unpack (n+1) a=(Nat.unpair a).1::unpack n (Nat.unpair a).2 := by
  simp only [unpack,List.range_succ_eq_map,List.map_cons,List.map_map,List.map_nil,
    List.cons_append,iterate_zero_apply,iterate_succ_apply]
  rfl

@[simp] theorem unpack_length (n a : ℕ) : (unpack n a).length=n+1 := by simp [unpack]

theorem unpack_ne_nil (n a : ℕ) : unpack n a≠[] := by
  intro h
  have he := congrArg List.length h
  rw [unpack_length] at he
  simp at he

def pack : List ℕ → ℕ
  | [] => 0
  | x::xs => if xs=[] then x else Nat.pair x (pack xs)

@[simp] theorem pack_singleton (x : ℕ) : pack [x]=x := rfl

theorem pack_unpack (n a : ℕ) : pack (unpack n a)=a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [unpack_succ,pack,if_neg (unpack_ne_nil n _),ih,Nat.pair_unpair]

theorem unpack_pack (xs : List ℕ) (hx : xs≠[]) :
    unpack (xs.length-1) (pack xs)=xs := by
  cases xs with
  | nil => exact (hx rfl).elim
  | cons x xs =>
    induction xs generalizing x with
    | nil => rfl
    | cons y ys ih =>
      simp only [List.length_cons,Nat.add_sub_cancel,pack,
        List.cons_ne_nil,if_false,unpack_succ,Nat.unpair_pair]
      simpa only [List.length_cons,Nat.add_sub_cancel,pack] using
        congrArg (List.cons x) (ih y (List.cons_ne_nil _ _))

def decode (n : ℕ) : List ℕ := unpack (Nat.unpair n).1 (Nat.unpair n).2
def encode (xs : List ℕ) : ℕ := Nat.pair (xs.length-1) (pack xs)

@[simp] theorem decode_encode (xs : List ℕ) (hx : xs≠[]) : decode (encode xs)=xs := by
  simp only [decode,encode,Nat.unpair_pair]
  exact unpack_pack xs hx

@[simp] theorem encode_decode (n : ℕ) : encode (decode n)=n := by
  simp [decode,encode,pack_unpack,Nat.pair_unpair]

theorem decode_ne_nil (n : ℕ) : decode n≠[] := unpack_ne_nil _ _

theorem unpack_computable : Computable₂ unpack := by
  have hi : Primrec (fun q : (ℕ × ℕ) × ℕ => tail^[q.2] q.1.2) :=
    Primrec.nat_iterate Primrec.snd (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to₂
  have hmap : Primrec (fun q : ℕ × ℕ =>
      (List.range q.1).map (fun i => (Nat.unpair (tail^[i] q.2)).1)) :=
    Primrec.list_map (Primrec.list_range.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.unpair.comp hi)).to₂
  have ht : Primrec (fun q : ℕ × ℕ => tail^[q.1] q.2) :=
    hi.comp (Primrec.pair Primrec.id Primrec.fst)
  exact (Primrec.list_append.comp hmap
    (Primrec.list_cons.comp ht (Primrec.const []))).to_comp

theorem pack_computable : Computable pack := by
  have hh : Primrec (fun q : List ℕ × ℕ × List ℕ × ℕ =>
      if q.2.2.1=[] then q.2.1 else Nat.pair q.2.1 q.2.2.2) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.const [])) (Primrec.fst.comp Primrec.snd)
      (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  apply Primrec.to_comp
  apply (Primrec.list_rec Primrec.id (Primrec.const 0) hh.to₂).of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simpa only [pack,id_eq] using congrArg (fun n => if xs=[] then x else Nat.pair x n) ih

theorem decode_computable : Computable decode :=
  unpack_computable.comp (Computable.fst.comp Computable.unpair)
    (Computable.snd.comp Computable.unpair)

theorem encode_computable : Computable encode :=
  Primrec₂.natPair.to_comp.comp
    (Primrec.nat_sub.to_comp.comp Primrec.list_length.to_comp (Computable.const 1)) pack_computable

end CategoricalEssentialIncompleteness.LocalConnectedness.WordCoding
