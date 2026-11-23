/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46JaniczakFOL
public import Foundation.FirstOrder.Syntax.Classical.PrimrecCoding

/-! # Computing Foundation sentence codes from the names of variables -/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder Encodable
namespace Janiczak.FOL.Coding

/-- Resolve the nearest binder for x, with the initial variables following the binders. -/
def lookup (base x : ℕ) (stack : List ℕ) : ℕ :=
  stack.foldr (fun y j => if y = x then 0 else j+1) (x % (base+1))

def names (base : ℕ) : (s : List ℕ) → Names (base+1+s.length)
  | [] => initialNames base
  | x::s => underBinder (names base s) x

private theorem lookup_names (base x : ℕ) (s : List ℕ) :
    (names base s x).val = lookup base x s := by
  induction s with
  | nil => rfl
  | cons y s ih =>
    by_cases h : x=y
    · simp [names, underBinder, h, lookup]
    · simpa [names, underBinder, h, lookup, Ne.symm h] using congrArg Nat.succ ih

/-- The syntax words for an atom, its negation, a Boolean connective and a quantifier. -/
def tag (k w : ℕ) := Nat.pair k w + 1
def pairWords (x y : ℕ) := Nat.pair x (Nat.pair y 0 + 1) + 1
def atom (sg rel x y : ℕ) := tag sg (Nat.pair 2 (Nat.pair rel (pairWords (tag 0 x) (tag 0 y))))
def binary (k x y : ℕ) := tag k (Nat.pair x y)

/-- Simultaneous codes for a formula and its classical negation. -/
def run : ℕ → ℕ → ℕ → List ℕ → ℕ × ℕ
  | 0, _, _, _ => (0,0)
  | k+1, word, base, s =>
    let t := word.unpair.1
    let z := word.unpair.2
    let x := z.unpair.1
    let y := z.unpair.2
    if t = 0 then (atom 0 0 (lookup base x s) (lookup base y s),
      atom 1 0 (lookup base x s) (lookup base y s))
    else if t = 1 then (atom 0 1 (lookup base x s) (lookup base y s),
      atom 1 1 (lookup base x s) (lookup base y s))
    else if t = 2 then (tag 2 0, tag 3 0)
    else if t = 3 then (run k z base s).swap
    else if t = 4 then
      let p := run k x base s
      let q := run k y base s
      (binary 4 p.1 q.1,binary 5 p.2 q.2)
    else if t = 5 then
      let p := run k y base (x::s)
      (tag 7 p.1, tag 6 p.2)
    else (0,0)

private theorem run_correct (p : Janiczak.Formula) (k : ℕ) (hk : p.depth ≤ k)
    (base : ℕ) (s : List ℕ) :
    run k p.code base s =
      (encode (translate p (names base s)), encode (∼(translate p (names base s)))) := by
  induction p generalizing k s with
  | equal x y =>
    cases k with
    | zero => simp [Janiczak.Formula.depth] at hk
    | succ k =>
      simp only [run, Janiczak.Formula.code, Nat.unpair_pair, ite_true, ← lookup_names]
      rfl
  | related x y =>
    cases k with
    | zero => simp [Janiczak.Formula.depth] at hk
    | succ k =>
      simp only [run, Janiczak.Formula.code, Nat.unpair_pair, Nat.reduceEqDiff, ite_false, ite_true,
        ← lookup_names]
      rfl
  | top =>
    cases k with
    | zero => simp [Janiczak.Formula.depth] at hk
    | succ k =>
      simp only [run, Janiczak.Formula.code, Nat.unpair_pair, Nat.reduceEqDiff, ite_false, ite_true]
      rfl
  | neg p ih =>
    cases k with
    | zero => simp [Janiczak.Formula.depth] at hk
    | succ k =>
      simp only [run, Janiczak.Formula.code, Nat.unpair_pair, Nat.reduceEqDiff, ite_false, ite_true,
        ih k (Nat.le_of_succ_le_succ hk) s, Prod.swap_prod_mk, translate]
      rw [show ∼∼translate p (names base s) = translate p (names base s) from Semiformula.neg_neg _]
  | conj p q ih jh =>
    cases k with
    | zero => simp [Janiczak.Formula.depth] at hk
    | succ k =>
      have h := Nat.le_of_succ_le_succ hk
      simp only [run, Janiczak.Formula.code, Nat.unpair_pair, Nat.reduceEqDiff, ite_false, ite_true,
        ih k ((Nat.le_max_left _ _).trans h) s, jh k ((Nat.le_max_right _ _).trans h) s]
      rfl
  | ex x p ih =>
    cases k with
    | zero => simp [Janiczak.Formula.depth] at hk
    | succ k =>
      simp only [run, Janiczak.Formula.code, Nat.unpair_pair, Nat.reduceEqDiff, ite_false, ite_true,
        ih k (Nat.le_of_succ_le_succ hk) (x::s)]
      rfl

abbrev State := ℕ × ℕ × ℕ × List ℕ
private def fuel (s : State) := s.1
private def key (s : State) := s.2.1.unpair.1
private def body (s : State) := s.2.1.unpair.2
private def left (s : State) := (body s).unpair.1
private def right (s : State) := (body s).unpair.2
private def base (s : State) := s.2.2.1
private def stack (s : State) := s.2.2.2

private def next (s : State) (w : ℕ) (l : List ℕ) : State := (fuel s-1,w,base s,l)
private def children (s : State) : List State :=
  if fuel s = 0 then [] else if key s = 3 then [next s (body s) (stack s)]
  else if key s = 4 then [next s (left s) (stack s),next s (right s) (stack s)]
  else if key s = 5 then [next s (right s) (left s::stack s)] else []

private def step (s : State) (outs : List (ℕ × ℕ)) :=
  let x := lookup (base s) (left s) (stack s)
  let y := lookup (base s) (right s) (stack s)
  let p := outs.getD 0 (0,0)
  let q := outs.getD 1 (0,0)
  if fuel s = 0 then (0,0)
  else if key s = 0 then (atom 0 0 x y,atom 1 0 x y)
  else if key s = 1 then (atom 0 1 x y,atom 1 1 x y)
  else if key s = 2 then (tag 2 0,tag 3 0)
  else if key s = 3 then p.swap
  else if key s = 4 then (binary 4 p.1 q.1,binary 5 p.2 q.2)
  else if key s = 5 then (tag 7 p.1,tag 6 p.2)
  else (0,0)

private theorem pFuel : Primrec fuel := Primrec.fst
private theorem pKey : Primrec key := Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))
private theorem pBody : Primrec body := Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))
private theorem pLeft : Primrec left := Primrec.fst.comp (Primrec.unpair.comp pBody)
private theorem pRight : Primrec right := Primrec.snd.comp (Primrec.unpair.comp pBody)
private theorem pBase : Primrec base := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
private theorem pStack : Primrec stack := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)

open Primrec in
private theorem pChildren : Primrec children := by
  have nxt {f : State → ℕ} {l : State → List ℕ} (hf : Primrec f) (hl : Primrec l) :
      Primrec (fun s => next s (f s) (l s)) := (nat_sub.comp pFuel (const 1)).pair (hf.pair (pBase.pair hl))
  exact ite (Primrec.eq.comp pFuel (const 0)) (const []) <|
    ite (Primrec.eq.comp pKey (const 3)) (list_cons.comp (nxt pBody pStack) (const [])) <|
    ite (Primrec.eq.comp pKey (const 4))
      (list_cons.comp (nxt pLeft pStack) (list_cons.comp (nxt pRight pStack) (const []))) <|
    ite (Primrec.eq.comp pKey (const 5))
      (list_cons.comp (nxt pRight (list_cons.comp pLeft pStack)) (const [])) (const [])

open Primrec in
private theorem pStep : Primrec₂ step := by
  have lk {f : State → ℕ} (hf : Primrec f) : Primrec (fun s => lookup (base s) (f s) (stack s)) :=
    list_foldr pStack (nat_mod.comp hf (succ.comp pBase))
      (to₂ (ite (Primrec.eq.comp (fst.comp snd) (hf.comp fst)) (const 0) (succ.comp (snd.comp snd))))
  have tg {α : Type} [Primcodable α] {f : α → ℕ} (k : ℕ) (h : Primrec f) :
      Primrec (fun a => tag k (f a)) := succ.comp (Primrec₂.natPair.comp (const k) h)
  have at' (sg rel : ℕ) : Primrec (fun s => atom sg rel
      (lookup (base s) (left s) (stack s)) (lookup (base s) (right s) (stack s))) :=
    tg sg (Primrec₂.natPair.comp (const 2) (Primrec₂.natPair.comp (const rel)
      (succ.comp (Primrec₂.natPair.comp (tg 0 (lk pLeft))
        (succ.comp (Primrec₂.natPair.comp (tg 0 (lk pRight)) (const 0)))))))
  let prv (n : ℕ) (x : State × List (ℕ × ℕ)) := x.2.getD n (0,0)
  have pp (n : ℕ) : Primrec (prv n) := (list_getD (0,0)).comp snd (const n)
  have chk (n : ℕ) := Primrec.eq.comp (pKey.comp (Primrec.fst (β := List (ℕ × ℕ)))) (const n)
  exact to₂ <| ite (Primrec.eq.comp (pFuel.comp fst) (const 0)) (const (0,0)) <|
    ite (chk 0) (((at' 0 0).pair (at' 1 0)).comp fst) <|
    ite (chk 1) (((at' 0 1).pair (at' 1 1)).comp fst) <|
    ite (chk 2) (const (tag 2 0,tag 3 0)) <|
    ite (chk 3) ((snd.comp (pp 0)).pair (fst.comp (pp 0))) <|
    ite (chk 4) ((tg 4 (Primrec₂.natPair.comp (fst.comp (pp 0)) (fst.comp (pp 1)))).pair
      (tg 5 (Primrec₂.natPair.comp (snd.comp (pp 0)) (snd.comp (pp 1))))) <|
    ite (chk 5) ((tg 7 (fst.comp (pp 0))).pair (tg 6 (snd.comp (pp 0)))) (const (0,0))

private def evaluate (s : State) := run s.1 s.2.1 s.2.2.1 s.2.2.2

private theorem dropFuel (s t : State) (ht : t ∈ children s) : fuel t < fuel s := by
  unfold children at ht
  split at ht
  · simp at ht
  next h =>
    split_ifs at ht <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    all_goals first | contradiction | (rcases ht with rfl | rfl <;> change fuel s-1 < fuel s <;> omega)

private theorem step_eq (s : State) : step s ((children s).map evaluate) = evaluate s := by
  rcases s with ⟨k,e,b,s⟩
  cases k with
  | zero => rfl
  | succ k =>
    simp only [step, children, evaluate, next, key, body, left, right, fuel, base, stack,
      Nat.succ_ne_zero, ite_false, Nat.add_one_sub_one, run]
    split_ifs <;> simp_all [evaluate, Prod.swap]

theorem primrec_run : Primrec (fun s : State ↦ run s.1 s.2.1 s.2.2.1 s.2.2.2) :=
  Primrec.nat_omega_rec' evaluate pFuel pChildren (Primrec.option_some.comp₂ pStep)
    dropFuel (fun s => congrArg some (step_eq s))

def close (n w : ℕ) : ℕ := Nat.rec w (fun _ v => tag 6 v) n

private theorem close_step (n w : ℕ) : close n (tag 6 w) = tag 6 (close n w) := by
  induction n with | zero => rfl | succ n ih => exact congrArg (tag 6) ih

private theorem encode_close {n : ℕ} (φ : Semisentence L n) :
    encode (∀¹* φ) = close n (encode φ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [allClosure_succ, ih, Semiformula.encode_all]
    exact close_step _ _

/-- A total primitive recursive forward translation on raw Gödel words. -/
def forward (w : ℕ) := close (w+1) (run (w+1) w w []).1

theorem forward_primrec : Primrec forward := by
  have hc : Primrec₂ close := Primrec.to₂ <| Primrec.nat_rec' Primrec.fst Primrec.snd
    (Primrec.to₂ (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 6) (Primrec.snd.comp Primrec.snd))))
  exact hc.comp Primrec.succ (Primrec.fst.comp (primrec_run.comp
    (Primrec.succ.pair (Primrec.id.pair (Primrec.id.pair (Primrec.const []))))))

theorem forward_code (p : Janiczak.Formula) : forward p.code = encode (sentence p) := by
  rw [forward, run_correct p _ p.depth_le_code, sentence, encode_close]
  rfl

end Janiczak.FOL.Coding
