/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46JaniczakCoding

/-!
# Evaluating formulas in finite equivalence structures

The left component of a paired number gives its equivalence-class label. A finite list gives the possible witnesses for each existential quantifier.
-/

@[expose] public section

set_option autoImplicit false

namespace Janiczak.FiniteEvaluator

/-- Members of a finite structure are numbers whose left unpairing component
is their equivalence-class label. -/
abbrev Env := List (ℕ × ℕ)

def value (env : Env) (x : ℕ) : ℕ := (env.lookup x).getD (Nat.pair (Nat.pair 1 0) 0)

theorem value_cons (env : Env) (x a : ℕ) :
    value ((x,a) :: env) = Function.update (value env) x a := by
  funext y
  by_cases h : y = x
  · simp [value, h, List.lookup]
  · simp [value, List.lookup, Function.update_of_ne h, beq_false_of_ne h]

/-- Bounded evaluation on a finite equivalence structure by recursion on the formula depth. -/
def run : ℕ → ℕ → List ℕ → Env → Bool
  | 0, _, _, _ => false
  | k+1, e, D, v =>
    let tag := e.unpair.1
    let z := e.unpair.2
    let x := z.unpair.1
    let y := z.unpair.2
    if tag = 0 then value v x == value v y
    else if tag = 1 then (value v x).unpair.1 == (value v y).unpair.1
    else if tag = 2 then true
    else if tag = 3 then !(run k z D v)
    else if tag = 4 then run k x D v && run k y D v
    else if tag = 5 then D.any (fun a ↦ run k y D ((x,a)::v))
    else false

abbrev State := ℕ × ℕ × List ℕ × Env

private def fuel (s : State) := s.1
private def key (s : State) := s.2.1.unpair.1
private def body (s : State) := s.2.1.unpair.2
private def left (s : State) := (body s).unpair.1
private def right (s : State) := (body s).unpair.2
private def domain (s : State) := s.2.2.1
private def env (s : State) := s.2.2.2

private def next (s : State) (e : ℕ) : State := (fuel s-1, e, domain s, env s)

private def children (s : State) : List State :=
  if fuel s = 0 then []
  else if key s = 3 then [next s (body s)]
  else if key s = 4 then [next s (left s), next s (right s)]
  else if key s = 5 then (domain s).map fun a ↦
    (fuel s-1, right s, domain s, (left s,a)::env s)
  else []

private def step (s : State) (v : List Bool) : Bool :=
  if fuel s = 0 then false
  else if key s = 0 then value (env s) (left s) == value (env s) (right s)
  else if key s = 1 then (value (env s) (left s)).unpair.1 == (value (env s) (right s)).unpair.1
  else if key s = 2 then true
  else if key s = 3 then !(v.getD 0 false)
  else if key s = 4 then v.getD 0 false && v.getD 1 false
  else if key s = 5 then v.any id
  else false

private theorem pFuel : Primrec fuel := Primrec.fst
private theorem pKey : Primrec key := Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))
private theorem pBody : Primrec body := Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))
private theorem pLeft : Primrec left := Primrec.fst.comp (Primrec.unpair.comp pBody)
private theorem pRight : Primrec right := Primrec.snd.comp (Primrec.unpair.comp pBody)
private theorem pDom : Primrec domain := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
private theorem pEnv : Primrec env := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)

private theorem pChildren : Primrec children := by
  open Primrec in
  have predFuel : Primrec (fun s ↦ fuel s-1) := nat_sub.comp pFuel (const 1)
  open Primrec in
  have nxt {f : State → ℕ} (hf : Primrec f) : Primrec (fun s ↦ next s (f s)) :=
    predFuel.pair (hf.pair (pDom.pair pEnv))
  open Primrec in
  have quant : Primrec (fun s ↦ (domain s).map fun a ↦
      (fuel s-1, right s, domain s, (left s,a)::env s)) :=
    list_map pDom (to₂ ((predFuel.comp fst).pair ((pRight.comp fst).pair
      ((pDom.comp fst).pair (list_cons.comp ((pLeft.comp fst).pair snd) (pEnv.comp fst))))))
  open Primrec in
  exact ite (Primrec.eq.comp pFuel (const 0)) (const []) <|
    ite (Primrec.eq.comp pKey (const 3)) (list_cons.comp (nxt pBody) (const [])) <|
    ite (Primrec.eq.comp pKey (const 4))
      (list_cons.comp (nxt pLeft) (list_cons.comp (nxt pRight) (const []))) <|
    ite (Primrec.eq.comp pKey (const 5)) quant (const [])

private theorem pStep : Primrec₂ step := by
  open Primrec in
  have val {f : State → ℕ} (hf : Primrec f) : Primrec (fun z : State × List Bool ↦ value (env z.1) (f z.1)) :=
    option_getD.comp (listLookup.comp (hf.comp fst) (pEnv.comp fst)) (const _)
  open Primrec in
  have lab {f : State → ℕ} (hf : Primrec f) :
      Primrec (fun z : State × List Bool ↦ (value (env z.1) (f z.1)).unpair.1) :=
    fst.comp (unpair.comp (val hf))
  open Primrec in
  have anyB : Primrec (fun v : List Bool ↦ v.any id) :=
    (list_foldr Primrec.id (const false) (to₂ (Primrec.or.comp (fst.comp snd) (snd.comp snd)))).of_eq
      (fun v ↦ by
        change v.foldr (· || ·) false = v.any id
        induction v with
        | nil => rfl
        | cons x xs ih => cases x <;> simp_all)
  open Primrec in
  exact to₂ <| ite (Primrec.eq.comp (pFuel.comp fst) (const 0)) (const false) <|
    ite (Primrec.eq.comp (pKey.comp fst) (const 0)) (Primrec.beq.comp (val pLeft) (val pRight)) <|
    ite (Primrec.eq.comp (pKey.comp fst) (const 1)) (Primrec.beq.comp (lab pLeft) (lab pRight)) <|
    ite (Primrec.eq.comp (pKey.comp fst) (const 2)) (const true) <|
    ite (Primrec.eq.comp (pKey.comp fst) (const 3)) (Primrec.not.comp ((list_getD false).comp snd (const 0))) <|
    ite (Primrec.eq.comp (pKey.comp fst) (const 4)) (Primrec.and.comp
      ((list_getD false).comp snd (const 0)) ((list_getD false).comp snd (const 1))) <|
    ite (Primrec.eq.comp (pKey.comp fst) (const 5)) (anyB.comp snd) (const false)

private def evaluate (s : State) := run s.1 s.2.1 s.2.2.1 s.2.2.2

private theorem children_decrease (s : State) (t : State) (ht : t ∈ children s) : fuel t < fuel s := by
  unfold children at ht
  split at ht
  · simp at ht
  next hf =>
    split at ht
    · simp only [List.mem_singleton] at ht
      rw [ht]
      change fuel s-1 < fuel s
      omega
    · split at ht
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl <;> change fuel s-1 < fuel s <;> omega
      · split at ht
        · simp only [List.mem_map] at ht
          obtain ⟨_, -, rfl⟩ := ht
          change fuel s-1 < fuel s
          omega
        · simp at ht

private theorem step_correct (s : State) :
    step s ((children s).map evaluate) = evaluate s := by
  rcases s with ⟨k,e,D,v⟩
  cases k with
  | zero => rfl
  | succ k =>
    simp only [step, children, evaluate, next, key, body, left, right, fuel, env, domain,
      Nat.succ_ne_zero, ite_false, Nat.add_one_sub_one, run]
    split_ifs <;> simp_all [List.any_map, evaluate, Function.comp_def]

theorem primrec_run : Primrec (fun s : State ↦ run s.1 s.2.1 s.2.2.1 s.2.2.2) :=
  Primrec.nat_omega_rec' evaluate pFuel pChildren (Primrec.option_some.comp₂ pStep)
    children_decrease (fun s ↦ congrArg some (step_correct s))

end Janiczak.FiniteEvaluator
