/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeContextSpecialization

/-!
# Numerical free-variable shifts

The full native proof calculus shifts free variables in both formulas and
finite-set sequents.  Bound variables remain unchanged, including below
nested quantifiers.  The raw operations below traverse numerical syntax;
the arity-guarded term/formula operations return zero on malformed syntax.
Raw operations follow their displayed numerical tags even for invalid codes;
the sequent operation inserts the guarded shift of each coded member.
A sequent is a finite-set code, not a list.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeSyntaxShift

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.NativeContextMP
open FailureOfComposition.NativeSubstitution

def vector₂Code (a b : ℕ) : ℕ :=
  Nat.pair a (Nat.pair b 0 + 1) + 1

def functionCode (k f v : ℕ) : ℕ :=
  Nat.pair 2 (Nat.pair k (Nat.pair f v)) + 1

def relationCode (tag k r v : ℕ) : ℕ :=
  Nat.pair tag (Nat.pair k (Nat.pair r v)) + 1

def firstTerm (e : ℕ) : ℕ :=
  (e.unpair.2.unpair.2.unpair.2 - 1).unpair.1

def secondTerm (e : ℕ) : ℕ :=
  ((e.unpair.2.unpair.2.unpair.2 - 1).unpair.2 - 1).unpair.1

private theorem firstTerm_lt (e : ℕ) : firstTerm e < e + 1 := by
  unfold firstTerm
  apply Nat.lt_succ_of_le
  exact le_trans (Nat.unpair_left_le _) <| le_trans (Nat.sub_le _ _) <|
    le_trans (Nat.unpair_right_le _) <|
      le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)

private theorem secondTerm_lt (e : ℕ) : secondTerm e < e + 1 := by
  unfold secondTerm
  apply Nat.lt_succ_of_le
  exact le_trans (Nat.unpair_left_le _) <| le_trans (Nat.sub_le _ _) <|
    le_trans (Nat.unpair_right_le _) <| le_trans (Nat.sub_le _ _) <|
      le_trans (Nat.unpair_right_le _) <|
        le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)

/-- Raw shift: bound variables are retained and free indices increase by one. -/
def termShiftRaw : ℕ → ℕ
  | 0 => 0
  | e + 1 =>
      if e.unpair.1 = 0 then Nat.pair 0 e.unpair.2 + 1
      else if e.unpair.1 = 1 then Nat.pair 1 (e.unpair.2 + 1) + 1
      else if e.unpair.1 = 2 then
        let k := e.unpair.2.unpair.1
        let f := e.unpair.2.unpair.2.unpair.1
        let v := e.unpair.2.unpair.2.unpair.2
        if k = 0 then functionCode 0 f v
        else if k = 2 then functionCode 2 f
          (vector₂Code (termShiftRaw (firstTerm e))
            (termShiftRaw (secondTerm e)))
        else 0
      else 0
termination_by e => e
decreasing_by
  · exact firstTerm_lt _
  · exact secondTerm_lt _

private def termLayer (history : List ℕ) (e : ℕ) : ℕ :=
  if e.unpair.1 = 0 then Nat.pair 0 e.unpair.2 + 1
  else if e.unpair.1 = 1 then Nat.pair 1 (e.unpair.2 + 1) + 1
  else if e.unpair.1 = 2 then
    let k := e.unpair.2.unpair.1
    let f := e.unpair.2.unpair.2.unpair.1
    let v := e.unpair.2.unpair.2.unpair.2
    if k = 0 then functionCode 0 f v
    else if k = 2 then functionCode 2 f
      (vector₂Code (history.getD (firstTerm e) 0)
        (history.getD (secondTerm e) 0))
    else 0
  else 0

private theorem primrec₂_vector₂Code : Primrec₂ vector₂Code :=
  (Primrec.succ.comp <| Primrec₂.natPair.comp Primrec.fst <|
    Primrec.succ.comp <| Primrec₂.natPair.comp Primrec.snd (Primrec.const 0)).to₂

private theorem primrec_functionCode {A : Type} [Primcodable A]
    {k f v : A → ℕ} (hk : Primrec k) (hf : Primrec f) (hv : Primrec v) :
    Primrec fun x => functionCode (k x) (f x) (v x) :=
  Primrec.succ.comp <| Primrec₂.natPair.comp (Primrec.const 2) <|
    Primrec₂.natPair.comp hk <| Primrec₂.natPair.comp hf hv

private theorem primrec_relationCode {A : Type} [Primcodable A]
    {tag k r v : A → ℕ} (htag : Primrec tag) (hk : Primrec k)
    (hr : Primrec r) (hv : Primrec v) :
    Primrec fun x => relationCode (tag x) (k x) (r x) (v x) :=
  Primrec.succ.comp <| Primrec₂.natPair.comp htag <|
    Primrec₂.natPair.comp hk <| Primrec₂.natPair.comp hr hv

private theorem primrec_firstTerm : Primrec firstTerm := by
  exact Primrec.fst.comp <| Primrec.unpair.comp <|
    Primrec.nat_sub.comp
      (Primrec.snd.comp <| Primrec.unpair.comp <|
        Primrec.snd.comp <| Primrec.unpair.comp <|
          Primrec.snd.comp Primrec.unpair) (Primrec.const 1)

private theorem primrec_secondTerm : Primrec secondTerm := by
  exact Primrec.fst.comp <| Primrec.unpair.comp <|
    Primrec.nat_sub.comp
      (Primrec.snd.comp <| Primrec.unpair.comp <|
        Primrec.nat_sub.comp
          (Primrec.snd.comp <| Primrec.unpair.comp <|
            Primrec.snd.comp <| Primrec.unpair.comp <|
              Primrec.snd.comp Primrec.unpair) (Primrec.const 1))
      (Primrec.const 1)

private theorem primrec₂_termLayer : Primrec₂ termLayer := by
  have hu := Primrec.unpair.comp (Primrec.snd (α := List ℕ) (β := ℕ))
  have htag := Primrec.fst.comp hu
  have hp := Primrec.snd.comp hu
  have hpu := Primrec.unpair.comp hp
  have hk := Primrec.fst.comp hpu
  have hrest := Primrec.unpair.comp (Primrec.snd.comp hpu)
  have hf := Primrec.fst.comp hrest
  have hv := Primrec.snd.comp hrest
  have hfirst := (Primrec.list_getD 0).comp Primrec.fst
    (primrec_firstTerm.comp Primrec.snd)
  have hsecond := (Primrec.list_getD 0).comp Primrec.fst
    (primrec_secondTerm.comp Primrec.snd)
  exact (Primrec.ite (Primrec.eq.comp htag (Primrec.const 0))
    (Primrec.succ.comp <| Primrec₂.natPair.comp (Primrec.const 0) hp) <|
    Primrec.ite (Primrec.eq.comp htag (Primrec.const 1))
      (Primrec.succ.comp <| Primrec₂.natPair.comp (Primrec.const 1)
        (Primrec.succ.comp hp)) <|
    Primrec.ite (Primrec.eq.comp htag (Primrec.const 2))
      (Primrec.ite (Primrec.eq.comp hk (Primrec.const 0))
        (primrec_functionCode (Primrec.const 0) hf hv) <|
        Primrec.ite (Primrec.eq.comp hk (Primrec.const 2))
          (primrec_functionCode (Primrec.const 2) hf
            (primrec₂_vector₂Code.comp hfirst hsecond)) (Primrec.const 0))
      (Primrec.const 0)).to₂

private theorem getD_history {A : Type} (f : ℕ → A) (n k : ℕ)
    (h : k < n) (default : A) :
    ((List.range n).map f).getD k default = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by simpa using h)]
  rfl

theorem primrec_termShiftRaw : Primrec termShiftRaw := by
  have h : Primrec₂ fun (_ : Unit) (n : ℕ) => termShiftRaw n := by
    apply Primrec.nat_strong_rec
      (fun (_ : Unit) (n : ℕ) => termShiftRaw n)
      (g := fun _ h => Nat.casesOn h.length (some 0)
        (fun e => some (termLayer h e)))
    · exact Primrec.nat_casesOn (Primrec.list_length.comp Primrec.snd)
        (Primrec.const (some 0))
        (Primrec.option_some.comp (primrec₂_termLayer.comp
          (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂
    · intro _ n
      cases n with
      | zero => simp [termShiftRaw]
      | succ e =>
          simp only [List.length_map, List.length_range]
          simp only [termLayer, termShiftRaw,
            getD_history _ _ _ (firstTerm_lt e) 0,
            getD_history _ _ _ (secondTerm_lt e) 0]
  exact h.comp (Primrec.const ()) Primrec.id

private def formulaLayer (history : List ℕ) (e : ℕ) : ℕ :=
  let tag := e.unpair.1
  let p := e.unpair.2
  if tag = 0 ∨ tag = 1 then
    relationCode tag 2 p.unpair.2.unpair.1
      (vector₂Code (termShiftRaw (firstTerm e))
        (termShiftRaw (secondTerm e)))
  else if tag = 2 ∨ tag = 3 then Nat.pair tag p + 1
  else if tag = 4 ∨ tag = 5 then
    Nat.pair tag (Nat.pair (history.getD p.unpair.1 0)
      (history.getD p.unpair.2 0)) + 1
  else if tag = 6 ∨ tag = 7 then
    Nat.pair tag (history.getD p 0) + 1
  else 0

/-- Raw formula shift, including formulas with any bound arity. -/
def formulaShiftRaw : ℕ → ℕ
  | 0 => 0
  | e + 1 =>
      let tag := e.unpair.1
      let p := e.unpair.2
      if tag = 0 ∨ tag = 1 then
        relationCode tag 2 p.unpair.2.unpair.1
          (vector₂Code (termShiftRaw (firstTerm e))
            (termShiftRaw (secondTerm e)))
      else if tag = 2 ∨ tag = 3 then Nat.pair tag p + 1
      else if tag = 4 ∨ tag = 5 then
        Nat.pair tag (Nat.pair (formulaShiftRaw p.unpair.1)
          (formulaShiftRaw p.unpair.2)) + 1
      else if tag = 6 ∨ tag = 7 then
        Nat.pair tag (formulaShiftRaw p) + 1
      else 0
termination_by p => p
decreasing_by
  all_goals
    apply Nat.lt_succ_of_le
    first
    | exact le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)
    | exact le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)
    | exact Nat.unpair_right_le _

private theorem primrec₂_formulaLayer : Primrec₂ formulaLayer := by
  have hu := Primrec.unpair.comp (Primrec.snd (α := List ℕ) (β := ℕ))
  have ht := Primrec.fst.comp hu
  have hp := Primrec.snd.comp hu
  have hpu := Primrec.unpair.comp hp
  have hfirst := (Primrec.list_getD 0).comp Primrec.fst (Primrec.fst.comp hpu)
  have hsecond := (Primrec.list_getD 0).comp Primrec.fst (Primrec.snd.comp hpu)
  have hbody := (Primrec.list_getD 0).comp Primrec.fst hp
  have hrel := primrec_relationCode ht (Primrec.const 2)
    (Primrec.fst.comp <| Primrec.unpair.comp <| Primrec.snd.comp hpu)
    (primrec₂_vector₂Code.comp
      (primrec_termShiftRaw.comp (primrec_firstTerm.comp Primrec.snd))
      (primrec_termShiftRaw.comp (primrec_secondTerm.comp Primrec.snd)))
  exact (Primrec.ite
    ((Primrec.eq.comp ht (Primrec.const 0)).or
      (Primrec.eq.comp ht (Primrec.const 1))) hrel <|
    Primrec.ite
      ((Primrec.eq.comp ht (Primrec.const 2)).or
        (Primrec.eq.comp ht (Primrec.const 3)))
      (Primrec.succ.comp <| Primrec₂.natPair.comp ht hp) <|
    Primrec.ite
      ((Primrec.eq.comp ht (Primrec.const 4)).or
        (Primrec.eq.comp ht (Primrec.const 5)))
      (Primrec.succ.comp <| Primrec₂.natPair.comp ht
        (Primrec₂.natPair.comp hfirst hsecond)) <|
    Primrec.ite
      ((Primrec.eq.comp ht (Primrec.const 6)).or
        (Primrec.eq.comp ht (Primrec.const 7)))
      (Primrec.succ.comp <| Primrec₂.natPair.comp ht hbody)
      (Primrec.const 0)).to₂

theorem primrec_formulaShiftRaw : Primrec formulaShiftRaw := by
  have h : Primrec₂ fun (_ : Unit) (n : ℕ) => formulaShiftRaw n := by
    apply Primrec.nat_strong_rec
      (fun (_ : Unit) (n : ℕ) => formulaShiftRaw n)
      (g := fun _ h => Nat.casesOn h.length (some 0)
        (fun e => some (formulaLayer h e)))
    · exact Primrec.nat_casesOn (Primrec.list_length.comp Primrec.snd)
        (Primrec.const (some 0))
        (Primrec.option_some.comp (primrec₂_formulaLayer.comp
          (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂
    · intro _ n
      cases n with
      | zero => simp [formulaShiftRaw]
      | succ e =>
          simp only [List.length_map, List.length_range]
          have h₁ : e.unpair.2.unpair.1 < e + 1 :=
            Nat.lt_succ_of_le (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _))
          have h₂ : e.unpair.2.unpair.2 < e + 1 :=
            Nat.lt_succ_of_le (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _))
          have h₃ : e.unpair.2 < e + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le _)
          simp only [formulaLayer, formulaShiftRaw,
            getD_history _ _ _ h₁ 0, getD_history _ _ _ h₂ 0,
            getD_history _ _ _ h₃ 0]
  exact h.comp (Primrec.const ()) Primrec.id

theorem termShiftRaw_encode {n : ℕ} (t : SyntacticSemiterm ℒₒᵣ n) :
    termShiftRaw (encode t) = encode (Rew.shift t) := by
  induction t with
  | bvar i => simp [termShiftRaw, Semiterm.encode_eq_toNat, Semiterm.toNat]
  | fvar x => simp [termShiftRaw, Semiterm.encode_eq_toNat, Semiterm.toNat]
  | func f v ih =>
      cases f <;>
        simp [termShiftRaw, functionCode, vector₂Code, firstTerm, secondTerm,
          Semiterm.encode_eq_toNat, Semiterm.toNat, Matrix.vecToNat,
          Matrix.vecHead, Matrix.vecTail, Rew.func]
      all_goals
        constructor
        · simpa only [Semiterm.encode_eq_toNat] using ih 0
        · simpa only [Semiterm.encode_eq_toNat] using ih 1

theorem formulaShiftRaw_encode {n : ℕ} (φ : ArithmeticSemiproposition n) :
    formulaShiftRaw (encode φ) = encode (Rewriting.shift φ) := by
  induction φ using Semiformula.rec' with
  | hverum => simp [formulaShiftRaw, Semiformula.encode_eq_toNat, Semiformula.toNat]
  | hfalsum => simp [formulaShiftRaw, Semiformula.encode_eq_toNat, Semiformula.toNat]
  | hrel r v =>
      cases r
      all_goals
        simp [formulaShiftRaw, relationCode, vector₂Code, firstTerm, secondTerm,
          Semiformula.encode_eq_toNat, Semiformula.toNat, Matrix.vecToNat,
          Matrix.vecHead, Matrix.vecTail,
          Semiterm.encode_eq_toNat]
      all_goals
        constructor
        · simpa only [Semiterm.encode_eq_toNat] using termShiftRaw_encode (v 0)
        · simpa only [Semiterm.encode_eq_toNat] using termShiftRaw_encode (v 1)
  | hnrel r v =>
      cases r
      all_goals
        simp [formulaShiftRaw, relationCode, vector₂Code, firstTerm, secondTerm,
          Semiformula.encode_eq_toNat, Semiformula.toNat, Matrix.vecToNat,
          Matrix.vecHead, Matrix.vecTail,
          Semiterm.encode_eq_toNat]
      all_goals
        constructor
        · simpa only [Semiterm.encode_eq_toNat] using termShiftRaw_encode (v 0)
        · simpa only [Semiterm.encode_eq_toNat] using termShiftRaw_encode (v 1)
  | hand φ ψ ihφ ihψ =>
      simpa [formulaShiftRaw, Semiformula.encode_eq_toNat, Semiformula.toNat]
        using And.intro ihφ ihψ
  | hor φ ψ ihφ ihψ =>
      simpa [formulaShiftRaw, Semiformula.encode_eq_toNat, Semiformula.toNat]
        using And.intro ihφ ihψ
  | hall φ ih =>
      simpa [formulaShiftRaw, Semiformula.encode_eq_toNat, Semiformula.toNat]
        using ih
  | hexs φ ih =>
      simpa [formulaShiftRaw, Semiformula.encode_eq_toNat, Semiformula.toNat]
        using ih

/-- Guarded numerical shift at a fixed bound arity. -/
def formulaShiftCode (n p : ℕ) : ℕ :=
  if (decode₂ (ArithmeticSemiproposition n) p).isSome then formulaShiftRaw p else 0

theorem primrec_formulaShiftCode (n : ℕ) : Primrec (formulaShiftCode n) := by
  exact Primrec.ite
    (Primrec.eq.comp (Primrec.option_isSome.comp
      (Primrec.decode₂ (α := ArithmeticSemiproposition n))) (Primrec.const true))
    primrec_formulaShiftRaw (Primrec.const 0)

theorem formulaShiftCode_eq_shift {n p : ℕ} (hp : IsSemiformula ℒₒᵣ n p) :
    formulaShiftCode n p = shift ℒₒᵣ p := by
  rcases hp.sound with ⟨φ, rfl⟩
  rw [← Semiformula.quote_shift]
  simp only [Semiformula.quote_eq_encode_nat]
  simp [formulaShiftCode, formulaShiftRaw_encode]

/-- Open a universal body by shifting free indices and inserting free zero. -/
def formulaFreeCode (p : ℕ) : ℕ :=
  subst1Code (encode (&0 : SyntacticTerm ℒₒᵣ)) (formulaShiftCode 1 p)

theorem primrec_formulaFreeCode : Primrec formulaFreeCode :=
  primrec₂_subst1Code.comp (Primrec.const _) (primrec_formulaShiftCode 1)

theorem formulaFreeCode_eq_free {p : ℕ} (hp : IsSemiformula ℒₒᵣ 1 p) :
    formulaFreeCode p = free ℒₒᵣ p := by
  unfold formulaFreeCode free
  rw [formulaShiftCode_eq_shift hp]
  have ht : IsTerm ℒₒᵣ (encode (&0 : SyntacticTerm ℒₒᵣ)) := by
    rw [← Semiterm.quote_eq_encode_standard]
    simp
  rw [subst1Code_eq_substs1 ht hp.shift]
  congr 1
  exact (Semiterm.quote_eq_encode_standard (&0 : SyntacticTerm ℒₒᵣ)).symm

/-- Guarded term shift at a fixed bound arity. -/
def termShiftCode (n t : ℕ) : ℕ :=
  if (decode₂ (SyntacticSemiterm ℒₒᵣ n) t).isSome then termShiftRaw t else 0

theorem primrec_termShiftCode (n : ℕ) : Primrec (termShiftCode n) := by
  exact Primrec.ite
    (Primrec.eq.comp (Primrec.option_isSome.comp
      (Primrec.decode₂ (α := SyntacticSemiterm ℒₒᵣ n))) (Primrec.const true))
    primrec_termShiftRaw (Primrec.const 0)

theorem termShiftCode_eq_termShift {n t : ℕ} (ht : IsSemiterm ℒₒᵣ n t) :
    termShiftCode n t = termShift ℒₒᵣ t := by
  rcases ht.sound with ⟨u, rfl⟩
  calc
    termShiftCode n (⌜u⌝ : ℕ) = encode (Rew.shift u) := by
      rw [Semiterm.quote_eq_encode_standard]
      simp [termShiftCode, termShiftRaw_encode]
    _ = (⌜Rew.shift u⌝ : ℕ) := (Semiterm.quote_eq_encode_standard _).symm
    _ = termShift ℒₒᵣ (⌜u⌝ : ℕ) :=
      congrArg Bootstrapping.Semiterm.val (Semiterm.typed_quote_shift (V := ℕ) u)

/-- Recognize finite sets containing only proposition codes. -/
def formulaSetCodeValid (s : ℕ) : Bool :=
  decide (∀ p ∈ List.range s, s / 2 ^ p % 2 = 1 → formulaCodeValid p = true)

/-- Map the guarded proposition shift over a finite-set sequent code. -/
def sequentShiftCode (s : ℕ) : ℕ :=
  (List.range s).foldr
    (fun p t => if s / 2 ^ p % 2 = 1 then
      sequentInsertCode (formulaShiftCode 0 p) t else t) 0

theorem primrecPred_sequentMem :
    PrimrecPred fun z : ℕ × ℕ => z.1 / 2 ^ z.2 % 2 = 1 := by
  have hp : Primrec fun z : ℕ × ℕ => 2 ^ z.2 :=
    (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.snd
  exact Primrec.eq.comp
    (Primrec.nat_mod.comp (Primrec.nat_div.comp Primrec.fst hp) (Primrec.const 2))
    (Primrec.const 1)

theorem primrecPred_formulaSetCodeValid :
    PrimrecPred fun s => formulaSetCodeValid s = true := by
  have h : PrimrecPred fun z : ℕ × ℕ =>
      z.1 / 2 ^ z.2 % 2 = 1 → formulaCodeValid z.2 = true :=
    (primrecPred_sequentMem.not.or
      (primrecPred_formulaCodeValid.comp Primrec.snd)).of_eq fun z => by
        exact imp_iff_not_or.symm
  exact ((h.comp (Primrec.snd.pair Primrec.fst)).primrecRel.forall_mem_list.comp
    Primrec.list_range Primrec.id).of_eq fun s => by
      simp [formulaSetCodeValid]

theorem formulaSetCodeValid_iff (s : ℕ) :
    formulaSetCodeValid s = true ↔ IsFormulaSet ℒₒᵣ s := by
  simp only [formulaSetCodeValid, decide_eq_true_eq, List.mem_range,
    formulaCodeValid_iff_isFormula]
  constructor
  · intro h p hp
    exact h p (lt_of_mem hp) (nat_mem_iff.mp hp)
  · intro h p _ hp
    exact h p (nat_mem_iff.mpr hp)

theorem primrec_sequentShiftCode : Primrec sequentShiftCode := by
  unfold sequentShiftCode
  apply Primrec.list_foldr Primrec.list_range (Primrec.const 0)
    (h := fun s pt => if s / 2 ^ pt.1 % 2 = 1 then
      sequentInsertCode (formulaShiftCode 0 pt.1) pt.2 else pt.2)
  exact (Primrec.ite
    (primrecPred_sequentMem.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
    (primrec₂_sequentInsertCode.comp
      ((primrec_formulaShiftCode 0).comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)).to₂

private theorem mem_shiftFold (s : ℕ) (l : List ℕ) (y : ℕ) :
    y ∈ l.foldr (fun p t => if s / 2 ^ p % 2 = 1 then
      sequentInsertCode (formulaShiftCode 0 p) t else t) 0 ↔
      ∃ p ∈ l, p ∈ s ∧ y = formulaShiftCode 0 p := by
  induction l with
  | nil => simp
  | cons p l ih =>
      by_cases hp : s / 2 ^ p % 2 = 1
      · rw [List.foldr_cons, ite_eq_left hp,
          show sequentInsertCode (formulaShiftCode 0 p)
            (l.foldr (fun p t => if s / 2 ^ p % 2 = 1 then
              sequentInsertCode (formulaShiftCode 0 p) t else t) 0) =
            insert (formulaShiftCode 0 p)
              (l.foldr (fun p t => if s / 2 ^ p % 2 = 1 then
                sequentInsertCode (formulaShiftCode 0 p) t else t) 0) from
            (nat_insert_eq _ _).symm,
          mem_bitInsert_iff, ih]
        simp only [List.mem_cons]
        constructor
        · rintro (h | ⟨q, hq, hqs, hy⟩)
          · exact ⟨p, Or.inl rfl, nat_mem_iff.mpr hp, h⟩
          · exact ⟨q, Or.inr hq, hqs, hy⟩
        · rintro ⟨q, (rfl | hq), hqs, hy⟩
          · exact Or.inl hy
          · exact Or.inr ⟨q, hq, hqs, hy⟩
      · simp only [List.foldr_cons, hp, ↓reduceIte, ih, List.mem_cons]
        constructor
        · rintro ⟨q, hq, hqs, hy⟩
          exact ⟨q, Or.inr hq, hqs, hy⟩
        · rintro ⟨q, (rfl | hq), hqs, hy⟩
          · exact False.elim (hp (nat_mem_iff.mp hqs))
          · exact ⟨q, hq, hqs, hy⟩

theorem sequentShiftCode_eq_setShift {s : ℕ} (hs : IsFormulaSet ℒₒᵣ s) :
    sequentShiftCode s = setShift ℒₒᵣ s := by
  apply mem_ext
  intro y
  rw [sequentShiftCode, mem_shiftFold, mem_setShift_iff]
  constructor
  · rintro ⟨p, _, hps, hy⟩
    exact ⟨p, hps, hy.trans (formulaShiftCode_eq_shift (hs p hps))⟩
  · rintro ⟨p, hps, hy⟩
    exact ⟨p, List.mem_range.mpr (lt_of_mem hps), hps,
      hy.trans (formulaShiftCode_eq_shift (hs p hps)).symm⟩

theorem formulaShiftCode_eq_zero_of_invalid {n p : ℕ}
    (hp : ¬IsSemiformula ℒₒᵣ n p) : formulaShiftCode n p = 0 := by
  unfold formulaShiftCode
  split_ifs with h
  · obtain ⟨φ, hφ⟩ := Option.isSome_iff_exists.mp h
    have he := decode₂_eq_some.mp hφ
    apply False.elim
    apply hp
    rw [← he, ← Semiformula.quote_eq_encode_nat]
    simpa using Semiformula.quote_isSemiformula (V := ℕ) φ
  · rfl

theorem termShiftCode_eq_zero_of_invalid {n t : ℕ}
    (ht : ¬IsSemiterm ℒₒᵣ n t) : termShiftCode n t = 0 := by
  unfold termShiftCode
  split_ifs with h
  · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h
    have he := decode₂_eq_some.mp hu
    apply False.elim
    apply ht
    rw [← he, ← Semiterm.quote_eq_encode_standard]
    simpa [Semiterm.quote_def] using
      (⌜u⌝ : Bootstrapping.Semiterm ℕ ℒₒᵣ n).isSemiterm
  · rfl

/-- Free-variable shift commutes with a nested quantifier; it does not
increment its bound variable. -/
theorem nested_shift_example (φ : ArithmeticSemiproposition 2) :
    formulaShiftRaw (encode (∀¹ φ)) = encode (∀¹ Rewriting.shift φ) := by
  simpa using formulaShiftRaw_encode (∀¹ φ)

theorem bound_free_shift_example :
    termShiftRaw (encode (#0 : SyntacticSemiterm ℒₒᵣ 1)) =
        encode (#0 : SyntacticSemiterm ℒₒᵣ 1) ∧
      termShiftRaw (encode (&0 : SyntacticSemiterm ℒₒᵣ 1)) =
        encode (&1 : SyntacticSemiterm ℒₒᵣ 1) := by
  constructor
  · simpa using termShiftRaw_encode (#0 : SyntacticSemiterm ℒₒᵣ 1)
  · simpa using termShiftRaw_encode (&0 : SyntacticSemiterm ℒₒᵣ 1)

end FailureOfComposition.NativeSyntaxShift
