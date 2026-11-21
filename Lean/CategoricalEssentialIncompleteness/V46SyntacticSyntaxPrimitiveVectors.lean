/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxWords
public import Foundation.Vorspiel.Computability

/-! # Standard primitive-recursion certificates for canonical vector operations -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.NatVectors

/-- Canonical zero/one-plus-pair list encoding, with no extra witness data. -/
def pack (l : List ℕ) : ℕ := l.foldr (fun x a => Nat.pair x a + 1) 0
@[simp] theorem pack_nil : pack [] = 0 := rfl
@[simp] theorem pack_cons (x : ℕ) (l : List ℕ) : pack (x :: l) = Nat.pair x (pack l) + 1 := rfl

 theorem pack_primrec : Primrec pack := by
  have hs : Primrec₂ (fun (_ : List ℕ) (p : ℕ × ℕ) => Nat.pair p.1 p.2 + 1) :=
    Primrec.to₂ <| Primrec.succ.comp <| Primrec₂.natPair.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec.of_eq (Primrec.list_foldr Primrec.id (Primrec.const 0) hs) (fun _ => rfl)

@[simp] theorem natToList_adjoin (x a : ℕ) :
    Nat.natToList (adjoin x a) = x :: Nat.natToList a := by
  rw [FiniteSigmaOne.canonical_adjoin, nat_pair_eq]
  rw [Nat.natToList.eq_def]
  simp only [Nat.unpair_pair]

@[simp] theorem pack_natToList (a : ℕ) : pack (Nat.natToList a) = a := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
      cases a with
      | zero => simp [Nat.natToList, pack]
      | succ n =>
          rw [Nat.natToList, pack_cons, ih n.unpair.2 (Nat.lt_succ_of_le (Nat.unpair_right_le n))]
          simp

@[simp] theorem natToList_pack (l : List ℕ) : Nat.natToList (pack l) = l := by
  induction l with
  | nil => simp [Nat.natToList]
  | cons x xs ih => simp [Nat.natToList, ih]

 theorem pack_injective : Function.Injective pack := by
  intro l r h
  simpa using congrArg Nat.natToList h

 theorem adjoin_primrec : Primrec₂ (adjoin : ℕ → ℕ → ℕ) := by
  have h : Primrec₂ (fun x a : ℕ => Nat.pair x a + 1) := Primrec.succ.comp Primrec₂.natPair
  exact Primrec.of_eq h fun p => by rw [FiniteSigmaOne.canonical_adjoin, nat_pair_eq]

/-- The model-level vector recursor agrees, on standard numbers, with
an ordinary list recursion on the same canonical decoded data. -/
def fold {k : ℕ} {B : VecRec.Blueprint k} (c : VecRec.Construction ℕ B)
    (params : Fin k → ℕ) (l : List ℕ) : ℕ :=
  l.recOn (c.nil params) (fun x xs ih => c.adjoin params x (pack xs) ih)

 theorem vecRec_eq_fold {k : ℕ} {B : VecRec.Blueprint k} (c : VecRec.Construction ℕ B)
    (params : Fin k → ℕ) (a : ℕ) : c.result params a = fold c params (Nat.natToList a) := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
      cases a with
      | zero => simp [fold, Nat.natToList]
      | succ n =>
          have hc : n + 1 = adjoin n.unpair.1 n.unpair.2 := by
            rw [FiniteSigmaOne.canonical_adjoin, nat_pair_eq]
            simp
          rw [hc, VecRec.Construction.result_adjoin, natToList_adjoin]
          change c.adjoin params n.unpair.1 n.unpair.2 (c.result params n.unpair.2) =
            c.adjoin params n.unpair.1 (pack (Nat.natToList n.unpair.2))
              (fold c params (Nat.natToList n.unpair.2))
          rw [pack_natToList, ih n.unpair.2 (Nat.lt_succ_of_le (Nat.unpair_right_le n))]

/-- This closure theorem proves a standard certificate from certificates for the nil and
cons computations. It makes no inference about nonstandard models from standard
extensional equality. -/
 theorem vecRec_primrec {α : Type*} [Primcodable α] {k : ℕ} {B : VecRec.Blueprint k}
    (c : VecRec.Construction ℕ B) (params : α → Fin k → ℕ)
    (hnil : Primrec (fun a => c.nil (params a)))
    (hstep : Primrec₂ (fun a (t : ℕ × List ℕ × ℕ) =>
      c.adjoin (params a) t.1 (pack t.2.1) t.2.2)) :
    Primrec (fun p : α × ℕ => c.result (params p.1) p.2) := by
  have hl : Primrec (fun p : α × ℕ => fold c (params p.1) (Nat.natToList p.2)) := by
    simpa only [fold] using Primrec.list_rec
      (Primrec.nat_natToList.comp Primrec.snd) (hnil.comp Primrec.fst)
      (Primrec.to₂ <| Primrec.comp hstep (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))
  exact hl.of_eq fun p => (vecRec_eq_fold c (params p.1) p.2).symm

 theorem append_primrec : Primrec₂ (Words.append : ℕ → ℕ → ℕ) := by
  have hn : Primrec (fun b : ℕ => (Words.appendConstruction (M := ℕ)).nil ![b]) := by
    change Primrec (fun b : ℕ => b)
    exact Primrec.id
  have hs : Primrec₂ (fun (b : ℕ) (t : ℕ × List ℕ × ℕ) =>
      (Words.appendConstruction (M := ℕ)).adjoin ![b] t.1 (pack t.2.1) t.2.2) := by
    simpa [Words.appendConstruction] using
      (Primrec.to₂ <| adjoin_primrec.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have h := vecRec_primrec (Words.appendConstruction (M := ℕ)) (fun b : ℕ => ![b]) hn hs
  exact Primrec.of_eq (h.comp (Primrec.pair Primrec.snd Primrec.fst)) (fun _ => rfl)

 theorem concat_primrec : Primrec₂ (concat : ℕ → ℕ → ℕ) := by
  have hsingle : Primrec (fun p : ℕ × ℕ => adjoin p.2 0) := adjoin_primrec.comp Primrec.snd (Primrec.const 0)
  have h := append_primrec.comp Primrec.fst hsingle
  exact h.of_eq fun p => Words.append_singleton p.1 p.2

 theorem len_eq_decode (a : ℕ) : len a = (Nat.natToList a).length := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
      cases a with
      | zero => simp [Nat.natToList]
      | succ n =>
          have hc : n + 1 = adjoin n.unpair.1 n.unpair.2 := by
            rw [FiniteSigmaOne.canonical_adjoin, nat_pair_eq]
            simp
          rw [hc, natToList_adjoin]
          simp [ih n.unpair.2 (Nat.lt_succ_of_le (Nat.unpair_right_le n))]

 theorem len_primrec : Primrec (len : ℕ → ℕ) :=
  (Primrec.list_length.comp Primrec.nat_natToList).of_eq fun a => (len_eq_decode a).symm

 theorem nth_eq_decode (a i : ℕ) : nth a i = (Nat.natToList a).getD i 0 := by
  induction a using Nat.strong_induction_on generalizing i with
  | h a ih =>
      cases a with
      | zero => simp [Nat.natToList]
      | succ n =>
          have hc : n + 1 = adjoin n.unpair.1 n.unpair.2 := by
            rw [FiniteSigmaOne.canonical_adjoin, nat_pair_eq]
            simp
          rw [hc, natToList_adjoin]
          cases i with
          | zero => simp
          | succ j =>
              rw [nth_adjoin_succ, List.getD_cons_succ]
              exact ih n.unpair.2 (Nat.lt_succ_of_le (Nat.unpair_right_le n)) j

 theorem nth_primrec : Primrec₂ (nth : ℕ → ℕ → ℕ) := by
  have h : Primrec (fun p : ℕ × ℕ => (Nat.natToList p.1).getD p.2 0) :=
    (Primrec.list_getD 0).comp (Primrec.nat_natToList.comp Primrec.fst) Primrec.snd
  exact h.of_eq fun p => (nth_eq_decode p.1 p.2).symm

 theorem pr_eq_natRec {k : ℕ} {B : PR.Blueprint k} (c : PR.Construction ℕ B)
    (params : Fin k → ℕ) (n : ℕ) :
    c.result params n = n.rec (c.zero params) (fun i prev => c.succ params i prev) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [PR.Construction.result_succ, ih]

 theorem pr_primrec {α : Type*} [Primcodable α] {k : ℕ} {B : PR.Blueprint k}
    (c : PR.Construction ℕ B) (params : α → Fin k → ℕ)
    (hz : Primrec (fun a => c.zero (params a)))
    (hs : Primrec₂ (fun a (t : ℕ × ℕ) => c.succ (params a) t.1 t.2)) :
    Primrec (fun p : α × ℕ => c.result (params p.1) p.2) := by
  have h := Primrec.nat_rec hz hs
  exact Primrec.of_eq h fun p => (pr_eq_natRec c (params p.1) p.2).symm

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.NatVectors
