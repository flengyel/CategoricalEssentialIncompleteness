/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46JaniczakNativeSyntax

/-!
# Primitive recursive translation of Foundation sentence codes

The native Gödel numbering determines the constructor, the class-relation symbol and the bound-variable indices. Translation gives the code of a formula with named variables.
-/

@[expose] public section

set_option autoImplicit false

namespace Janiczak.NativeInput

open FFL FFL.FirstOrder FFL.FirstOrder.Language Encodable
open FFL.FirstOrder.Semiterm FFL.FirstOrder.Semiformula

/-- A canonical Foundation word is the standard code of a well-formed semisentence. -/
def valid (n e : ℕ) := ∃ p : Semisentence ℒₛₑₜ n, encode p = e

private theorem valid_iff (n e : ℕ) :
    valid n e ↔ encode (Semiformula.ofNat (L := ℒₛₑₜ) (ξ := Empty) n e) = e+1 := by
  change valid n e ↔ encode (decode e : Option (Semisentence ℒₛₑₜ n)) = e+1
  constructor
  · rintro ⟨p,rfl⟩
    simp
  · intro hh
    cases hp : (decode e : Option (Semisentence ℒₛₑₜ n)) with
    | none => simp [hp] at hh
    | some p =>
      rw [hp] at hh
      exact ⟨p, Nat.succ_inj.mp hh⟩

theorem primrec_validWord : PrimrecPred (fun q : ℕ × ℕ ↦ ∃ p : Semisentence ℒₛₑₜ q.1, encode p = q.2) :=
  (Primrec.eq.comp (Semiformula.encode_ofNat_primrec (L := ℒₛₑₜ) (ξ := Empty))
    (Primrec.succ.comp Primrec.snd)).of_eq fun q ↦ (valid_iff q.1 q.2).symm

/-- The number assigned to the named translation of a Foundation formula word. -/
noncomputable def namedWord (q : ℕ × ℕ) : ℕ :=
  open Classical in
  if h : valid q.1 q.2 then (named h.choose).code else 0

@[simp] theorem namedWord_encode {n : ℕ} (p : Semisentence ℒₛₑₜ n) :
    namedWord (n,encode p) = (named p).code := by
  have h : valid n (encode p) := ⟨p,rfl⟩
  rw [namedWord, dite_eq_left h]
  exact congrArg (fun p ↦ (named p).code) (Encodable.encode_injective h.choose_spec)

/-- Variable names on encoded terms read their de Bruijn index. -/
private def varCode (n e : ℕ) := n-((e-1).unpair.2+1)

private theorem varCode_encode {n : ℕ} (t : Semiterm ℒₛₑₜ Empty n) :
    varCode n (encode t) = name t := by
  cases t with
  | bvar i =>
    change n-((Nat.pair 0 i.val+1-1).unpair.2+1) = n-(i.val+1)
    simp
  | fvar x => exact x.elim
  | func f _ => exact Empty.elim f

private def tag (e : ℕ) := (e-1).unpair.1
private def payload (e : ℕ) := (e-1).unpair.2

private def termPairCode (n v : ℕ) :=
  Nat.pair (varCode n (tag v)) (varCode n (tag (payload v)))

private def symbol (p : ℕ) := p.unpair.2.unpair.1
private def argVector (p : ℕ) := p.unpair.2.unpair.2

private def atomic (n p : ℕ) := Nat.pair (symbol p) (termPairCode n (argVector p))

private theorem atomCode {n a : ℕ} (R : (ℒₛₑₜ).Rel a) (v : Fin a → Semiterm ℒₛₑₜ Empty n) :
    atomic n (Nat.pair a (Nat.pair (encode R) (Matrix.vecToNat fun i ↦ encode (v i)))) =
      (atom R v).code := by
  cases R with
  | eq =>
    rw [Matrix.fun_eq_vec_two (fun i ↦ encode (v i))]
    simp only [atomic, symbol, argVector, termPairCode, tag, payload, Matrix.encode_succ, Matrix.vecToNat_empty, Nat.unpair_pair,
      Nat.add_one_sub_one, varCode_encode]
    rfl
  | mem =>
    rw [Matrix.fun_eq_vec_two (fun i ↦ encode (v i))]
    simp only [atomic, symbol, argVector, termPairCode, tag, payload, Matrix.encode_succ, Matrix.vecToNat_empty, Nat.unpair_pair,
      Nat.add_one_sub_one, varCode_encode]
    rfl

private def recArgs (q : ℕ × ℕ) : List (ℕ × ℕ) :=
  let n := q.1
  let e := q.2
  let t := tag e
  let p := payload e
  if e = 0 then []
  else if t=4 ∨ t=5 then [(n,p.unpair.1),(n,p.unpair.2)]
  else if t=6 ∨ t=7 then [(n+1,p)]
  else []

private def assemble (n t p r s : ℕ) :=
  if t=0 then atomic n p
  else if t=1 then Nat.pair 3 (atomic n p)
  else if t=2 then Janiczak.Formula.top.code
  else if t=3 then Janiczak.Formula.top.neg.code
  else if t=4 then Nat.pair 4 (Nat.pair r s)
  else if t=5 then Nat.pair 3 (Nat.pair 4 (Nat.pair (Nat.pair 3 r) (Nat.pair 3 s)))
  else if t=6 then Nat.pair 3 (Nat.pair 5 (Nat.pair n (Nat.pair 3 r)))
  else Nat.pair 5 (Nat.pair n r)

private noncomputable def step (q : ℕ × ℕ) (rs : List ℕ) :=
  open Classical in if valid q.1 q.2 then
    assemble q.1 (tag q.2) (payload q.2) (rs.getD 0 0) (rs.getD 1 0) else 0

private theorem pTag : Primrec tag := Primrec.fst.comp (Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))
private theorem pPayload : Primrec payload := Primrec.snd.comp (Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))
private theorem pVar : Primrec₂ varCode := Primrec.to₂ <| Primrec.nat_sub.comp Primrec.fst
  (Primrec.succ.comp (pPayload.comp Primrec.snd))

private theorem pArgs : Primrec recArgs := by
  open Primrec in
  have binary : Primrec (fun q : ℕ × ℕ ↦ [(q.1,(payload q.2).unpair.1),(q.1,(payload q.2).unpair.2)]) :=
    list_cons.comp (fst.pair (fst.comp (unpair.comp (pPayload.comp snd))))
      (list_cons.comp (fst.pair (snd.comp (unpair.comp (pPayload.comp snd)))) (const []))
  open Primrec in
  have qual : Primrec (fun q : ℕ × ℕ ↦ [(q.1+1,payload q.2)]) :=
    list_cons.comp ((succ.comp fst).pair (pPayload.comp snd)) (const [])
  open Primrec in
  exact ite (Primrec.eq.comp snd (const 0)) (const []) <|
    ite ((Primrec.eq.comp (pTag.comp snd) (const 4)).or (Primrec.eq.comp (pTag.comp snd) (const 5))) binary <|
    ite ((Primrec.eq.comp (pTag.comp snd) (const 6)).or (Primrec.eq.comp (pTag.comp snd) (const 7))) qual (const [])

private theorem pPairTerms : Primrec₂ termPairCode := by
  open Primrec in
  exact to₂ <| Primrec₂.natPair.comp (pVar.comp fst (pTag.comp snd))
    (pVar.comp fst (pTag.comp (pPayload.comp snd)))

private theorem pSymbol : Primrec symbol :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

private theorem pVector : Primrec argVector :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

private theorem pAtomic : Primrec₂ atomic := by
  have h₁ : Primrec (fun q : ℕ × ℕ ↦ symbol q.2) := pSymbol.comp Primrec.snd
  have h₂ : Primrec (fun q : ℕ × ℕ ↦ termPairCode q.1 (argVector q.2)) :=
    pPairTerms.comp Primrec.fst (pVector.comp Primrec.snd)
  exact (Primrec₂.natPair.comp h₁ h₂ : Primrec (fun q : ℕ × ℕ ↦ Nat.pair (symbol q.2)
    (termPairCode q.1 (argVector q.2))))

private theorem pStep : Primrec₂ step := by
  classical
  let A := (ℕ × ℕ) × List ℕ
  let n : A → ℕ := fun q ↦ q.1.1
  let t : A → ℕ := fun q ↦ tag q.1.2
  let p : A → ℕ := fun q ↦ payload q.1.2
  let r : A → ℕ := fun q ↦ q.2.getD 0 0
  let s : A → ℕ := fun q ↦ q.2.getD 1 0
  open Primrec in
  have hn : Primrec n := fst.comp fst
  open Primrec in
  have ht : Primrec t := pTag.comp (snd.comp fst)
  open Primrec in
  have hp : Primrec p := pPayload.comp (snd.comp fst)
  open Primrec in
  have hr : Primrec r := (list_getD 0).comp snd (const 0)
  open Primrec in
  have hs : Primrec s := (list_getD 0).comp snd (const 1)
  open Primrec in
  have pair (i : ℕ) {f : A → ℕ} (hf : Primrec f) : Primrec (fun a ↦ Nat.pair i (f a)) :=
    Primrec₂.natPair.comp (const i) hf
  open Primrec in
  have cmp (i : ℕ) : PrimrecPred (fun q ↦ t q = i) := Primrec.eq.comp ht (const i)
  open Primrec in
  exact to₂ <| ite (primrec_validWord.comp fst)
    (ite (cmp 0) (pAtomic.comp hn hp) <|
     ite (cmp 1) (pair 3 (pAtomic.comp hn hp)) <|
     ite (cmp 2) (const Janiczak.Formula.top.code) <|
     ite (cmp 3) (const Janiczak.Formula.top.neg.code) <|
     ite (cmp 4) (pair 4 (Primrec₂.natPair.comp hr hs)) <|
     ite (cmp 5) (pair 3 (pair 4 (Primrec₂.natPair.comp (pair 3 hr) (pair 3 hs)))) <|
     ite (cmp 6) (pair 3 (pair 5 (Primrec₂.natPair.comp hn (pair 3 hr))))
       (pair 5 (Primrec₂.natPair.comp hn hr))) (const 0)

private theorem args_ord (q w : ℕ × ℕ) (h : w ∈ recArgs q) : w.2 < q.2 := by
  simp only [recArgs] at h
  split at h
  · simp at h
  next he =>
    have hle : payload q.2 ≤ q.2-1 := Nat.unpair_right_le _
    have l := Nat.unpair_left_le (payload q.2)
    have r := Nat.unpair_right_le (payload q.2)
    split at h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> dsimp only <;> omega
    · split at h
      · simp only [List.mem_singleton] at h
        rw [h]
        exact Nat.lt_of_le_of_lt hle (by omega)
      · simp at h

private theorem step_encode {n : ℕ} (p : Semisentence ℒₛₑₜ n) :
    step (n,encode p) ((recArgs (n,encode p)).map namedWord) = (named p).code := by
  have hv : valid n (encode p) := ⟨p,rfl⟩
  simp only [step,hv,ite_true]
  cases p with
  | rel R v =>
    rw [Semiformula.encode_rel]
    simpa [assemble,tag,payload,named] using atomCode R v
  | nrel R v =>
    rw [Semiformula.encode_nrel]
    simpa [assemble,tag,payload,named,Janiczak.Formula.code] using congrArg (Nat.pair 3) (atomCode R v)
  | verum =>
    change assemble n (tag (Nat.pair 2 0+1)) _ _ _ = Janiczak.Formula.top.code
    simp [assemble,tag]
  | falsum =>
    change assemble n (tag (Nat.pair 3 0+1)) _ _ _ = Janiczak.Formula.top.neg.code
    simp [assemble,tag]
  | and p q =>
    have he : encode (Semiformula.and p q) = Nat.pair 4 (Nat.pair (encode p) (encode q))+1 := rfl
    rw [he]
    simp [assemble,tag,payload,recArgs,named,Janiczak.Formula.code]
  | or p q =>
    have he : encode (Semiformula.or p q) = Nat.pair 5 (Nat.pair (encode p) (encode q))+1 := rfl
    rw [he]
    simp [assemble,tag,payload,recArgs,named,Janiczak.Formula.disj,Janiczak.Formula.code]
  | all p =>
    have he : encode (Semiformula.all p) = Nat.pair 6 (encode p)+1 := rfl
    rw [he]
    simp [assemble,tag,payload,recArgs,named,Janiczak.Formula.all,Janiczak.Formula.code]
  | exs p =>
    have he : encode (Semiformula.exs p) = Nat.pair 7 (encode p)+1 := rfl
    rw [he]
    simp [assemble,tag,payload,recArgs,named,Janiczak.Formula.code]

theorem primrec_namedWord : Primrec namedWord := by
  classical
  refine Primrec.nat_omega_rec' namedWord Primrec.snd pArgs (Primrec.option_some.comp₂ pStep)
    args_ord ?_
  intro q
  rcases q with ⟨n,e⟩
  by_cases h : valid n e
  · obtain ⟨p,rfl⟩ := h
    exact congrArg some ((step_encode p).trans (namedWord_encode p).symm)
  · simp [step,namedWord,h]

end Janiczak.NativeInput
