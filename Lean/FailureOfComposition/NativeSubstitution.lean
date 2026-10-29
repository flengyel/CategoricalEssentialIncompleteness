/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Functions
import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Coding
import Foundation.FirstOrder.Syntax.Classical.PrimrecCoding

/-!
# Uniform numerical substitution for arithmetic syntax

The numerical input `t` is a code of a syntactic arithmetic term with no
bound variables, and `p` is a code of a syntactic arithmetic formula with one
bound variable.  Free variables may occur in both inputs.  On valid inputs,
`subst1Code t p` is the code obtained by substituting `t` for the single bound
variable of `p`; malformed inputs return zero.

The raw recursion carries the number `d` of intervening binders.  At depth
`d`, bound variables below `d` belong to inner quantifiers, while bound
variable `d` is the variable being replaced.  This makes the binder-shifting
convention explicit before the public depth-zero operation is defined.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeSubstitution

open FFL.FirstOrder.Arithmetic.Bootstrapping

abbrev ArithmeticSyntacticTerm := SyntacticTerm ℒₒᵣ

abbrev ArithmeticFormulaBody := ArithmeticSemiproposition 1

private def binaryVectorCode (a b : ℕ) : ℕ :=
  Nat.pair a (Nat.pair b 0 + 1) + 1

private def functionCode (arity symbol vector : ℕ) : ℕ :=
  Nat.pair 2 (Nat.pair arity (Nat.pair symbol vector)) + 1

private def relationCode (tag arity symbol vector : ℕ) : ℕ :=
  Nat.pair tag (Nat.pair arity (Nat.pair symbol vector)) + 1

/-- Substitute a depth-zero term code into a term code under `d` binders.
Only the arities of the fixed ordered-ring language are traversed: constants
have arity zero, and addition and multiplication have arity two. -/
def termSubstAtCode (t d : ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 =>
      let tag := e.unpair.1
      let payload := e.unpair.2
      if tag = 0 then
        if payload < d then Nat.pair 0 payload + 1
        else if payload = d then t
        else 0
      else if tag = 1 then Nat.pair 1 payload + 1
      else if tag = 2 then
        let arity := payload.unpair.1
        let symbolAndVector := payload.unpair.2
        let symbol := symbolAndVector.unpair.1
        let vector := symbolAndVector.unpair.2
        if arity = 0 then functionCode 0 symbol vector
        else if arity = 2 then
          let first := (vector - 1).unpair.1
          let tail := (vector - 1).unpair.2
          let second := (tail - 1).unpair.1
          functionCode 2 symbol
            (binaryVectorCode (termSubstAtCode t d first)
              (termSubstAtCode t d second))
        else 0
      else 0
termination_by e => e
decreasing_by
  all_goals
    apply Nat.lt_succ_of_le
    first
    | exact le_trans (Nat.unpair_left_le _)
        (le_trans (Nat.sub_le _ _) <|
          le_trans (Nat.unpair_right_le _)
            (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)))
    | exact le_trans (Nat.unpair_left_le _)
        (le_trans (Nat.sub_le _ _) <|
          le_trans (Nat.unpair_right_le _)
            (le_trans (Nat.sub_le _ _) <|
              le_trans (Nat.unpair_right_le _)
                (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _))))

private theorem primrec₂_binaryVectorCode : Primrec₂ binaryVectorCode := by
  exact (Primrec.succ.comp <|
    Primrec₂.natPair.comp Primrec.fst <|
      Primrec.succ.comp <|
        Primrec₂.natPair.comp Primrec.snd (Primrec.const 0)).to₂

private theorem primrec_functionCode {A : Type} [Primcodable A]
    {arity symbol vector : A → ℕ}
    (harity : Primrec arity) (hsymbol : Primrec symbol)
    (hvector : Primrec vector) :
    Primrec fun x => functionCode (arity x) (symbol x) (vector x) := by
  exact Primrec.succ.comp <|
    Primrec₂.natPair.comp (Primrec.const 2) <|
      Primrec₂.natPair.comp harity <|
        Primrec₂.natPair.comp hsymbol hvector

private def termSubstStep (td : ℕ × ℕ) (history : List ℕ) : Option ℕ :=
  Nat.casesOn history.length (some 0) fun e =>
    let tag := e.unpair.1
    let payload := e.unpair.2
    some <|
      if tag = 0 then
        if payload < td.2 then Nat.pair 0 payload + 1
        else if payload = td.2 then td.1
        else 0
      else if tag = 1 then Nat.pair 1 payload + 1
      else if tag = 2 then
        let arity := payload.unpair.1
        let symbolAndVector := payload.unpair.2
        let symbol := symbolAndVector.unpair.1
        let vector := symbolAndVector.unpair.2
        if arity = 0 then functionCode 0 symbol vector
        else if arity = 2 then
          let first := (vector - 1).unpair.1
          let tail := (vector - 1).unpair.2
          let second := (tail - 1).unpair.1
          functionCode 2 symbol
            (binaryVectorCode (history.getD first 0)
              (history.getD second 0))
        else 0
      else 0

private theorem primrec₂_termSubstStep : Primrec₂ termSubstStep := by
  change Primrec fun x : (ℕ × ℕ) × List ℕ => termSubstStep x.1 x.2
  have hstep : Primrec fun x : (((ℕ × ℕ) × List ℕ) × ℕ) =>
      some <|
        if x.2.unpair.1 = 0 then
          if x.2.unpair.2 < x.1.1.2 then
            Nat.pair 0 x.2.unpair.2 + 1
          else if x.2.unpair.2 = x.1.1.2 then x.1.1.1
          else 0
        else if x.2.unpair.1 = 1 then
          Nat.pair 1 x.2.unpair.2 + 1
        else if x.2.unpair.1 = 2 then
          if x.2.unpair.2.unpair.1 = 0 then
            functionCode 0 x.2.unpair.2.unpair.2.unpair.1
              x.2.unpair.2.unpair.2.unpair.2
          else if x.2.unpair.2.unpair.1 = 2 then
            functionCode 2 x.2.unpair.2.unpair.2.unpair.1
              (binaryVectorCode
                (x.1.2.getD
                  ((x.2.unpair.2.unpair.2.unpair.2 - 1).unpair.1) 0)
                (x.1.2.getD
                  ((((x.2.unpair.2.unpair.2.unpair.2 - 1).unpair.2) - 1).unpair.1) 0))
          else 0
        else 0 := by
    have ht : Primrec fun x : (((ℕ × ℕ) × List ℕ) × ℕ) => x.1.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have hd : Primrec fun x : (((ℕ × ℕ) × List ℕ) × ℕ) => x.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have hh : Primrec fun x : (((ℕ × ℕ) × List ℕ) × ℕ) => x.1.2 :=
      Primrec.snd.comp Primrec.fst
    have he : Primrec fun x : (((ℕ × ℕ) × List ℕ) × ℕ) => x.2 :=
      Primrec.snd
    have hu := Primrec.unpair.comp he
    have htag := Primrec.fst.comp hu
    have hpayload := Primrec.snd.comp hu
    have hpu := Primrec.unpair.comp hpayload
    have harity := Primrec.fst.comp hpu
    have hsymbolVector := Primrec.snd.comp hpu
    have hsvu := Primrec.unpair.comp hsymbolVector
    have hsymbol := Primrec.fst.comp hsvu
    have hvector := Primrec.snd.comp hsvu
    have hvectorPred := Primrec.nat_sub.comp hvector (Primrec.const 1)
    have hvpu := Primrec.unpair.comp hvectorPred
    have hfirst := Primrec.fst.comp hvpu
    have htail := Primrec.snd.comp hvpu
    have htailPred := Primrec.nat_sub.comp htail (Primrec.const 1)
    have htpu := Primrec.unpair.comp htailPred
    have hsecond := Primrec.fst.comp htpu
    have hgetFirst := (Primrec.list_getD 0).comp hh hfirst
    have hgetSecond := (Primrec.list_getD 0).comp hh hsecond
    have hbvar : Primrec fun x : (((ℕ × ℕ) × List ℕ) × ℕ) =>
        if x.2.unpair.2 < x.1.1.2 then Nat.pair 0 x.2.unpair.2 + 1
        else if x.2.unpair.2 = x.1.1.2 then x.1.1.1
        else 0 :=
      Primrec.ite (Primrec.nat_lt.comp hpayload hd)
        (Primrec.succ.comp <| Primrec₂.natPair.comp (Primrec.const 0) hpayload) <|
        Primrec.ite (Primrec.eq.comp hpayload hd) ht (Primrec.const 0)
    have hfvar : Primrec fun x : (((ℕ × ℕ) × List ℕ) × ℕ) =>
        Nat.pair 1 x.2.unpair.2 + 1 :=
      Primrec.succ.comp <| Primrec₂.natPair.comp (Primrec.const 1) hpayload
    have hfuncZero := primrec_functionCode (Primrec.const 0) hsymbol hvector
    have hmappedVector := primrec₂_binaryVectorCode.comp hgetFirst hgetSecond
    have hfuncTwo := primrec_functionCode (Primrec.const 2) hsymbol hmappedVector
    have hfunc : Primrec fun x : (((ℕ × ℕ) × List ℕ) × ℕ) =>
        if x.2.unpair.2.unpair.1 = 0 then
          functionCode 0 x.2.unpair.2.unpair.2.unpair.1
            x.2.unpair.2.unpair.2.unpair.2
        else if x.2.unpair.2.unpair.1 = 2 then
          functionCode 2 x.2.unpair.2.unpair.2.unpair.1
            (binaryVectorCode
              (x.1.2.getD
                ((x.2.unpair.2.unpair.2.unpair.2 - 1).unpair.1) 0)
              (x.1.2.getD
                ((((x.2.unpair.2.unpair.2.unpair.2 - 1).unpair.2) - 1).unpair.1) 0))
        else 0 :=
      Primrec.ite (Primrec.eq.comp harity (Primrec.const 0)) hfuncZero <|
        Primrec.ite (Primrec.eq.comp harity (Primrec.const 2)) hfuncTwo
          (Primrec.const 0)
    exact Primrec.option_some.comp <|
      Primrec.ite (Primrec.eq.comp htag (Primrec.const 0)) hbvar <|
      Primrec.ite (Primrec.eq.comp htag (Primrec.const 1)) hfvar <|
      Primrec.ite (Primrec.eq.comp htag (Primrec.const 2)) hfunc
        (Primrec.const 0)
  exact Primrec.nat_casesOn (Primrec.list_length.comp Primrec.snd)
    (Primrec.const (some 0)) hstep.to₂

private theorem getD_map_range {A : Type} (f : ℕ → A) (n k : ℕ)
    (h : k < n) (default : A) :
    ((List.range n).map f).getD k default = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by simpa using h)]
  rfl

private theorem termFirst_lt (e : ℕ) :
    ((e.unpair.2.unpair.2.unpair.2 - 1).unpair.1) < e + 1 := by
  apply Nat.lt_succ_of_le
  exact le_trans (Nat.unpair_left_le _)
    (le_trans (Nat.sub_le _ _) <|
      le_trans (Nat.unpair_right_le _)
        (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)))

private theorem termSecond_lt (e : ℕ) :
    ((((e.unpair.2.unpair.2.unpair.2 - 1).unpair.2) - 1).unpair.1) <
      e + 1 := by
  apply Nat.lt_succ_of_le
  exact le_trans (Nat.unpair_left_le _)
    (le_trans (Nat.sub_le _ _) <|
      le_trans (Nat.unpair_right_le _)
        (le_trans (Nat.sub_le _ _) <|
          le_trans (Nat.unpair_right_le _)
            (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _))))

private theorem termSubstStep_history (td : ℕ × ℕ) (n : ℕ) :
    termSubstStep td ((List.range n).map
      (termSubstAtCode td.1 td.2)) =
      some (termSubstAtCode td.1 td.2 n) := by
  cases n with
  | zero => simp [termSubstStep, termSubstAtCode]
  | succ e =>
      have hlen : ((List.range (e + 1)).map
          (termSubstAtCode td.1 td.2)).length = e + 1 := by
        simp
      unfold termSubstStep
      rw [hlen]
      simp only
      rw [termSubstAtCode,
        getD_map_range _ (e + 1) _ (termFirst_lt e) 0,
        getD_map_range _ (e + 1) _ (termSecond_lt e) 0]

/-- The raw term operation is primitive recursive jointly in the replacement
code, binder depth, and input term code, packed as `((t,d),u)`. -/
theorem primrec_termSubstAtCodePacked :
    Primrec fun z : (ℕ × ℕ) × ℕ =>
      termSubstAtCode z.1.1 z.1.2 z.2 := by
  have hrec : Primrec₂ fun td : ℕ × ℕ => fun n : ℕ =>
      termSubstAtCode td.1 td.2 n := by
    apply Primrec.nat_strong_rec
      (fun (td : ℕ × ℕ) (n : ℕ) => termSubstAtCode td.1 td.2 n)
    · exact primrec₂_termSubstStep
    · exact termSubstStep_history
  exact Primrec₂.uncurry.mpr hrec

/-- Substitute into a formula code under `d` intervening binders.  Atomic
arithmetic relations have arity two; conjunctions, disjunctions, and
quantifiers recurse on their displayed subformula codes. -/
def formulaSubstAtCode (t d : ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 =>
      let tag := e.unpair.1
      let payload := e.unpair.2
      if tag = 0 ∨ tag = 1 then
        let arity := payload.unpair.1
        let symbolAndVector := payload.unpair.2
        let symbol := symbolAndVector.unpair.1
        let vector := symbolAndVector.unpair.2
        if arity = 2 then
          let first := (vector - 1).unpair.1
          let tail := (vector - 1).unpair.2
          let second := (tail - 1).unpair.1
          relationCode tag 2 symbol
            (binaryVectorCode (termSubstAtCode t d first)
              (termSubstAtCode t d second))
        else 0
      else if tag = 2 then Nat.pair 2 0 + 1
      else if tag = 3 then Nat.pair 3 0 + 1
      else if tag = 4 then
        Nat.pair 4
          (Nat.pair (formulaSubstAtCode t d payload.unpair.1)
            (formulaSubstAtCode t d payload.unpair.2)) + 1
      else if tag = 5 then
        Nat.pair 5
          (Nat.pair (formulaSubstAtCode t d payload.unpair.1)
            (formulaSubstAtCode t d payload.unpair.2)) + 1
      else if tag = 6 then
        Nat.pair 6 (formulaSubstAtCode t (d + 1) payload) + 1
      else if tag = 7 then
        Nat.pair 7 (formulaSubstAtCode t (d + 1) payload) + 1
      else 0
termination_by e => e
decreasing_by
  all_goals
    apply Nat.lt_succ_of_le
    first
    | exact le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)
    | exact le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)
    | exact Nat.unpair_right_le _

private theorem primrec_relationCode {A : Type} [Primcodable A]
    {tag arity symbol vector : A → ℕ}
    (htag : Primrec tag) (harity : Primrec arity)
    (hsymbol : Primrec symbol) (hvector : Primrec vector) :
    Primrec fun x => relationCode (tag x) (arity x) (symbol x) (vector x) := by
  exact Primrec.succ.comp <|
    Primrec₂.natPair.comp htag <|
      Primrec₂.natPair.comp harity <|
        Primrec₂.natPair.comp hsymbol hvector

private abbrev FormulaSubstState := (ℕ × ℕ) × ℕ

private def formulaSubstState (state : FormulaSubstState) : ℕ :=
  formulaSubstAtCode state.1.1 state.1.2 state.2

private def formulaSubArgs (state : FormulaSubstState) :
    List FormulaSubstState :=
  Nat.casesOn state.2 [] fun e =>
    let tag := e.unpair.1
    let payload := e.unpair.2
    if tag = 4 ∨ tag = 5 then
      [(state.1, payload.unpair.1), (state.1, payload.unpair.2)]
    else if tag = 6 ∨ tag = 7 then
      [((state.1.1, state.1.2 + 1), payload)]
    else []

private theorem primrec_formulaSubArgs : Primrec formulaSubArgs := by
  have hstep : Primrec fun x : FormulaSubstState × ℕ =>
      if x.2.unpair.1 = 4 ∨ x.2.unpair.1 = 5 then
        [(x.1.1, x.2.unpair.2.unpair.1),
          (x.1.1, x.2.unpair.2.unpair.2)]
      else if x.2.unpair.1 = 6 ∨ x.2.unpair.1 = 7 then
        [((x.1.1.1, x.1.1.2 + 1), x.2.unpair.2)]
      else [] := by
    have htd : Primrec fun x : FormulaSubstState × ℕ => x.1.1 :=
      Primrec.fst.comp Primrec.fst
    have ht : Primrec fun x : FormulaSubstState × ℕ => x.1.1.1 :=
      Primrec.fst.comp htd
    have hd : Primrec fun x : FormulaSubstState × ℕ => x.1.1.2 :=
      Primrec.snd.comp htd
    have he : Primrec fun x : FormulaSubstState × ℕ => x.2 :=
      Primrec.snd
    have hu := Primrec.unpair.comp he
    have htag := Primrec.fst.comp hu
    have hpayload := Primrec.snd.comp hu
    have hpu := Primrec.unpair.comp hpayload
    have hleftCode := Primrec.fst.comp hpu
    have hrightCode := Primrec.snd.comp hpu
    have hleftState := htd.pair hleftCode
    have hrightState := htd.pair hrightCode
    have hbinary := Primrec.list_cons.comp hleftState <|
      Primrec.list_cons.comp hrightState (Primrec.const [])
    have hnextTd := ht.pair (Primrec.succ.comp hd)
    have hquantState := hnextTd.pair hpayload
    have hquant := Primrec.list_cons.comp hquantState (Primrec.const [])
    exact Primrec.ite
      (PrimrecPred.or
        (Primrec.eq.comp htag (Primrec.const 4))
        (Primrec.eq.comp htag (Primrec.const 5))) hbinary <|
      Primrec.ite
        (PrimrecPred.or
          (Primrec.eq.comp htag (Primrec.const 6))
          (Primrec.eq.comp htag (Primrec.const 7))) hquant
        (Primrec.const [])
  exact Primrec.nat_casesOn (Primrec.snd)
    (Primrec.const []) hstep.to₂

private def formulaSubstStep
    (state : FormulaSubstState) (values : List ℕ) : Option ℕ :=
  Nat.casesOn state.2 (some 0) fun e =>
    let tag := e.unpair.1
    let payload := e.unpair.2
    some <|
      if tag = 0 ∨ tag = 1 then
        let arity := payload.unpair.1
        let symbolAndVector := payload.unpair.2
        let symbol := symbolAndVector.unpair.1
        let vector := symbolAndVector.unpair.2
        if arity = 2 then
          let first := (vector - 1).unpair.1
          let tail := (vector - 1).unpair.2
          let second := (tail - 1).unpair.1
          relationCode tag 2 symbol
            (binaryVectorCode
              (termSubstAtCode state.1.1 state.1.2 first)
              (termSubstAtCode state.1.1 state.1.2 second))
        else 0
      else if tag = 2 then Nat.pair 2 0 + 1
      else if tag = 3 then Nat.pair 3 0 + 1
      else if tag = 4 then
        Nat.pair 4 (Nat.pair (values.getD 0 0) (values.getD 1 0)) + 1
      else if tag = 5 then
        Nat.pair 5 (Nat.pair (values.getD 0 0) (values.getD 1 0)) + 1
      else if tag = 6 then Nat.pair 6 (values.getD 0 0) + 1
      else if tag = 7 then Nat.pair 7 (values.getD 0 0) + 1
      else 0

private theorem primrec₂_formulaSubstStep : Primrec₂ formulaSubstStep := by
  change Primrec fun x : FormulaSubstState × List ℕ =>
    formulaSubstStep x.1 x.2
  have hstep : Primrec fun x : ((FormulaSubstState × List ℕ) × ℕ) =>
      some <|
        if x.2.unpair.1 = 0 ∨ x.2.unpair.1 = 1 then
          if x.2.unpair.2.unpair.1 = 2 then
            relationCode x.2.unpair.1 2
              x.2.unpair.2.unpair.2.unpair.1
              (binaryVectorCode
                (termSubstAtCode x.1.1.1.1 x.1.1.1.2
                  ((x.2.unpair.2.unpair.2.unpair.2 - 1).unpair.1))
                (termSubstAtCode x.1.1.1.1 x.1.1.1.2
                  ((((x.2.unpair.2.unpair.2.unpair.2 - 1).unpair.2) - 1).unpair.1)))
          else 0
        else if x.2.unpair.1 = 2 then Nat.pair 2 0 + 1
        else if x.2.unpair.1 = 3 then Nat.pair 3 0 + 1
        else if x.2.unpair.1 = 4 then
          Nat.pair 4 (Nat.pair (x.1.2.getD 0 0) (x.1.2.getD 1 0)) + 1
        else if x.2.unpair.1 = 5 then
          Nat.pair 5 (Nat.pair (x.1.2.getD 0 0) (x.1.2.getD 1 0)) + 1
        else if x.2.unpair.1 = 6 then Nat.pair 6 (x.1.2.getD 0 0) + 1
        else if x.2.unpair.1 = 7 then Nat.pair 7 (x.1.2.getD 0 0) + 1
        else 0 := by
    have ht : Primrec fun x : ((FormulaSubstState × List ℕ) × ℕ) =>
        x.1.1.1.1 := Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hd : Primrec fun x : ((FormulaSubstState × List ℕ) × ℕ) =>
        x.1.1.1.2 := Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hvalues : Primrec fun x : ((FormulaSubstState × List ℕ) × ℕ) =>
        x.1.2 := Primrec.snd.comp Primrec.fst
    have he : Primrec fun x : ((FormulaSubstState × List ℕ) × ℕ) =>
        x.2 := Primrec.snd
    have hu := Primrec.unpair.comp he
    have htag := Primrec.fst.comp hu
    have hpayload := Primrec.snd.comp hu
    have hpu := Primrec.unpair.comp hpayload
    have harity := Primrec.fst.comp hpu
    have hsymbolVector := Primrec.snd.comp hpu
    have hsvu := Primrec.unpair.comp hsymbolVector
    have hsymbol := Primrec.fst.comp hsvu
    have hvector := Primrec.snd.comp hsvu
    have hvectorPred := Primrec.nat_sub.comp hvector (Primrec.const 1)
    have hvpu := Primrec.unpair.comp hvectorPred
    have hfirstCode := Primrec.fst.comp hvpu
    have htail := Primrec.snd.comp hvpu
    have htailPred := Primrec.nat_sub.comp htail (Primrec.const 1)
    have htpu := Primrec.unpair.comp htailPred
    have hsecondCode := Primrec.fst.comp htpu
    have htermFirst := primrec_termSubstAtCodePacked.comp <|
      (ht.pair hd).pair hfirstCode
    have htermSecond := primrec_termSubstAtCodePacked.comp <|
      (ht.pair hd).pair hsecondCode
    have hmappedVector := primrec₂_binaryVectorCode.comp htermFirst htermSecond
    have hrelation := primrec_relationCode htag (Primrec.const 2)
      hsymbol hmappedVector
    have hatom : Primrec fun x : ((FormulaSubstState × List ℕ) × ℕ) =>
        if x.2.unpair.2.unpair.1 = 2 then
          relationCode x.2.unpair.1 2
            x.2.unpair.2.unpair.2.unpair.1
            (binaryVectorCode
              (termSubstAtCode x.1.1.1.1 x.1.1.1.2
                ((x.2.unpair.2.unpair.2.unpair.2 - 1).unpair.1))
              (termSubstAtCode x.1.1.1.1 x.1.1.1.2
                ((((x.2.unpair.2.unpair.2.unpair.2 - 1).unpair.2) - 1).unpair.1)))
        else 0 :=
      Primrec.ite (Primrec.eq.comp harity (Primrec.const 2)) hrelation
        (Primrec.const 0)
    have hgetZero := (Primrec.list_getD 0).comp hvalues (Primrec.const 0)
    have hgetOne := (Primrec.list_getD 0).comp hvalues (Primrec.const 1)
    have hbinary (tag : ℕ) : Primrec fun x : ((FormulaSubstState × List ℕ) × ℕ) =>
        Nat.pair tag (Nat.pair (x.1.2.getD 0 0) (x.1.2.getD 1 0)) + 1 :=
      Primrec.succ.comp <|
        Primrec₂.natPair.comp (Primrec.const tag) <|
          Primrec₂.natPair.comp hgetZero hgetOne
    have hquant (tag : ℕ) : Primrec fun x : ((FormulaSubstState × List ℕ) × ℕ) =>
        Nat.pair tag (x.1.2.getD 0 0) + 1 :=
      Primrec.succ.comp <|
        Primrec₂.natPair.comp (Primrec.const tag) hgetZero
    have hconstant (tag : ℕ) : Primrec fun _x : ((FormulaSubstState × List ℕ) × ℕ) =>
        Nat.pair tag 0 + 1 := Primrec.const _
    exact Primrec.option_some.comp <|
      Primrec.ite
        (PrimrecPred.or
          (Primrec.eq.comp htag (Primrec.const 0))
          (Primrec.eq.comp htag (Primrec.const 1))) hatom <|
      Primrec.ite (Primrec.eq.comp htag (Primrec.const 2)) (hconstant 2) <|
      Primrec.ite (Primrec.eq.comp htag (Primrec.const 3)) (hconstant 3) <|
      Primrec.ite (Primrec.eq.comp htag (Primrec.const 4)) (hbinary 4) <|
      Primrec.ite (Primrec.eq.comp htag (Primrec.const 5)) (hbinary 5) <|
      Primrec.ite (Primrec.eq.comp htag (Primrec.const 6)) (hquant 6) <|
      Primrec.ite (Primrec.eq.comp htag (Primrec.const 7)) (hquant 7)
        (Primrec.const 0)
  exact Primrec.nat_casesOn (Primrec.snd.comp Primrec.fst)
    (Primrec.const (some 0)) hstep.to₂

private theorem formulaSubArgs_ord
    (state : FormulaSubstState) (child : FormulaSubstState)
    (hchild : child ∈ formulaSubArgs state) :
    child.2 < state.2 := by
  rcases state with ⟨td, _ | e⟩
  · simp [formulaSubArgs] at hchild
  · by_cases hbinary : e.unpair.1 = 4 ∨ e.unpair.1 = 5
    · have hcases :
          child = (td, e.unpair.2.unpair.1) ∨
            child = (td, e.unpair.2.unpair.2) := by
        simpa [formulaSubArgs, hbinary] using hchild
      rcases hcases with hleft | hright
      · subst child
        exact Nat.lt_succ_of_le <|
          le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)
      · subst child
        exact Nat.lt_succ_of_le <|
          le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)
    · by_cases hquant : e.unpair.1 = 6 ∨ e.unpair.1 = 7
      · have hcase : child = ((td.1, td.2 + 1), e.unpair.2) := by
          simpa [formulaSubArgs, hbinary, hquant] using hchild
        subst child
        exact Nat.lt_succ_of_le (Nat.unpair_right_le _)
      · simp [formulaSubArgs, hbinary, hquant] at hchild

private theorem formulaSubstStep_correct (state : FormulaSubstState) :
    formulaSubstStep state
        ((formulaSubArgs state).map formulaSubstState) =
      some (formulaSubstState state) := by
  rcases state with ⟨td, _ | e⟩
  · simp [formulaSubstStep, formulaSubArgs, formulaSubstState,
      formulaSubstAtCode]
  · by_cases h0 : e.unpair.1 = 0
    · simp_all [formulaSubstStep, formulaSubstState, formulaSubstAtCode]
    · by_cases h1 : e.unpair.1 = 1
      · simp_all [formulaSubstStep, formulaSubstState, formulaSubstAtCode]
      · by_cases h2 : e.unpair.1 = 2
        · simp_all [formulaSubstStep, formulaSubstState, formulaSubstAtCode]
        · by_cases h3 : e.unpair.1 = 3
          · simp_all [formulaSubstStep, formulaSubstState,
              formulaSubstAtCode]
          · by_cases h4 : e.unpair.1 = 4
            · simp_all [formulaSubstStep, formulaSubArgs,
                formulaSubstState, formulaSubstAtCode]
            · by_cases h5 : e.unpair.1 = 5
              · simp_all [formulaSubstStep, formulaSubArgs,
                  formulaSubstState, formulaSubstAtCode]
              · by_cases h6 : e.unpair.1 = 6
                · simp_all [formulaSubstStep, formulaSubArgs,
                    formulaSubstState, formulaSubstAtCode]
                · by_cases h7 : e.unpair.1 = 7
                  · simp_all [formulaSubstStep, formulaSubArgs,
                      formulaSubstState, formulaSubstAtCode]
                  · simp_all [formulaSubstStep, formulaSubstState,
                      formulaSubstAtCode]

/-- The raw formula operation is primitive recursive jointly in the
replacement code, binder depth, and input formula code, packed as
`((t,d),p)`. -/
theorem primrec_formulaSubstAtCodePacked : Primrec formulaSubstState := by
  exact Primrec.nat_omega_rec' formulaSubstState
    (m := fun state => state.2) (l := formulaSubArgs)
    (g := formulaSubstStep) (Primrec.snd) primrec_formulaSubArgs
    primrec₂_formulaSubstStep formulaSubArgs_ord formulaSubstStep_correct

/-- Numerical validity test for syntactic arithmetic terms of bound arity
zero.  Free variables are retained by using `SyntacticTerm`. -/
def termCodeValid (t : ℕ) : Bool :=
  (decode₂ ArithmeticSyntacticTerm t).isSome

/-- Numerical validity test for syntactic arithmetic formula bodies of bound
arity one. -/
def formulaBodyCodeValid (p : ℕ) : Bool :=
  (decode₂ ArithmeticFormulaBody p).isSome

theorem termCodeValid_iff_isSemiterm (t : ℕ) :
    termCodeValid t = true ↔ IsSemiterm ℒₒᵣ 0 t := by
  constructor
  · intro h
    have hsome : (decode₂ ArithmeticSyntacticTerm t).isSome := by
      simpa [termCodeValid] using h
    rcases Option.isSome_iff_exists.mp hsome with ⟨u, hu⟩
    have hcode : encode u = t := decode₂_eq_some.mp hu
    rw [← hcode]
    simpa [Semiterm.quote_eq_encode_standard] using
      (show IsSemiterm ℒₒᵣ 0 (⌜u⌝ : ℕ) by
        simp [Semiterm.quote_def])
  · intro h
    rcases h.sound with ⟨u, hu⟩
    have hcode : encode u = t := by
      simpa [Semiterm.quote_eq_encode_standard] using hu
    have hdecode : decode₂ ArithmeticSyntacticTerm t = some u :=
      decode₂_eq_some.mpr hcode
    simp [termCodeValid, hdecode]

theorem formulaBodyCodeValid_iff_isSemiformula (p : ℕ) :
    formulaBodyCodeValid p = true ↔ IsSemiformula ℒₒᵣ 1 p := by
  constructor
  · intro h
    have hsome : (decode₂ ArithmeticFormulaBody p).isSome := by
      simpa [formulaBodyCodeValid] using h
    rcases Option.isSome_iff_exists.mp hsome with ⟨φ, hφ⟩
    have hcode : encode φ = p := decode₂_eq_some.mp hφ
    rw [← hcode]
    have hquote := Semiformula.quote_isSemiformula (V := ℕ) φ
    rw [Semiformula.quote_eq_encode_nat] at hquote
    exact hquote
  · intro h
    rcases h.sound with ⟨φ, hφ⟩
    have hcode : encode φ = p := by
      simpa [Semiformula.quote_eq_encode_nat] using hφ
    have hdecode : decode₂ ArithmeticFormulaBody p = some φ :=
      decode₂_eq_some.mpr hcode
    simp [formulaBodyCodeValid, hdecode]

theorem primrecPred_termCodeValid :
    PrimrecPred fun t => termCodeValid t = true := by
  exact (Primrec.eq.comp
    (Primrec.option_isSome.comp
      (Primrec.decode₂ (α := ArithmeticSyntacticTerm)))
    (Primrec.const true)).of_eq fun t => by simp [termCodeValid]

theorem primrecPred_formulaBodyCodeValid :
    PrimrecPred fun p => formulaBodyCodeValid p = true := by
  exact (Primrec.eq.comp
    (Primrec.option_isSome.comp
      (Primrec.decode₂ (α := ArithmeticFormulaBody)))
    (Primrec.const true)).of_eq fun p => by simp [formulaBodyCodeValid]

/-- Total one-variable substitution on numerical codes.  Both codes vary;
malformed terms or formula bodies are sent to zero. -/
def subst1Code (t p : ℕ) : ℕ :=
  if termCodeValid t && formulaBodyCodeValid p then
    formulaSubstAtCode t 0 p
  else 0

/-- Substitution is primitive recursive jointly in the term and formula
codes. -/
theorem primrec₂_subst1Code : Primrec₂ subst1Code := by
  have hraw : Primrec fun z : ℕ × ℕ =>
      formulaSubstAtCode z.1 0 z.2 :=
    primrec_formulaSubstAtCodePacked.comp <|
      (Primrec.fst.pair (Primrec.const 0)).pair Primrec.snd
  have hvalid : PrimrecPred fun z : ℕ × ℕ =>
      termCodeValid z.1 = true ∧ formulaBodyCodeValid z.2 = true :=
    PrimrecPred.and
      (primrecPred_termCodeValid.comp Primrec.fst)
      (primrecPred_formulaBodyCodeValid.comp Primrec.snd)
  exact (Primrec.ite hvalid hraw (Primrec.const 0)).of_eq fun z => by
    simp [subst1Code, Bool.and_eq_true]

/-! ## Agreement with typed arithmetic syntax -/

private def liftTerm (t : ArithmeticSyntacticTerm) (d : ℕ) :
    SyntacticSemiterm ℒₒᵣ d :=
  Rew.castLE (Nat.zero_le d) t

private theorem liftTerm_encode (t : ArithmeticSyntacticTerm) (d : ℕ) :
    encode (liftTerm t d) = encode t := by
  induction t with
  | bvar i => exact i.elim0
  | fvar x => rfl
  | func f v ih =>
      simp only [liftTerm, Rew.func, Semiterm.encode_eq_toNat,
        Semiterm.toNat]
      congr 4
      apply congrArg Matrix.vecToNat
      funext i
      simpa only [liftTerm, Function.comp_apply, Semiterm.encode_eq_toNat]
        using ih i

private theorem bShift_liftTerm (t : ArithmeticSyntacticTerm) (d : ℕ) :
    Rew.bShift (liftTerm t d) = liftTerm t (d + 1) := by
  induction t with
  | bvar i => exact i.elim0
  | fvar x => rfl
  | func f v ih =>
      simp only [liftTerm, Rew.func]
      congr 1
      funext i
      exact ih i

private def substAtVec (t : ArithmeticSyntacticTerm) (d : ℕ) :
    Fin (d + 1) → SyntacticSemiterm ℒₒᵣ d := fun i =>
  if h : i.val < d then #⟨i.val, h⟩ else liftTerm t d

private theorem substAtVec_zero (t : ArithmeticSyntacticTerm) :
    substAtVec t 0 = ![t] := by
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  simp [substAtVec, liftTerm]

private theorem substAtVec_q (t : ArithmeticSyntacticTerm) (d : ℕ) :
    (Rew.subst (substAtVec t d)).q =
      Rew.subst (substAtVec t (d + 1)) := by
  rw [Rew.q_subst]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => simp [substAtVec]
  | succ j =>
      by_cases hj : j.val < d
      · have hsucc : j.val + 1 < d + 1 := Nat.add_lt_add_right hj 1
        simp [substAtVec, hj, hsucc]
      · have hsucc : ¬j.val + 1 < d + 1 := by omega
        simp [substAtVec, hj, hsucc, bShift_liftTerm]

private theorem termSubstAtCode_encode
    (t : ArithmeticSyntacticTerm) (d : ℕ) :
    ∀ u : SyntacticSemiterm ℒₒᵣ (d + 1),
      termSubstAtCode (encode t) d (encode u) =
        encode (Rew.subst (substAtVec t d) u) := by
  intro u
  induction u with
  | bvar i =>
      by_cases hi : i.val < d
      · simp [termSubstAtCode, substAtVec, hi,
          Semiterm.encode_eq_toNat, Semiterm.toNat]
      · have hieq : i.val = d := by omega
        simp [termSubstAtCode, substAtVec, hieq,
          Semiterm.encode_eq_toNat, Semiterm.toNat]
        simpa only [Semiterm.encode_eq_toNat] using (liftTerm_encode t d).symm
  | fvar x =>
      simp [termSubstAtCode, Semiterm.encode_eq_toNat, Semiterm.toNat]
  | func f v ih =>
      cases f with
      | zero =>
          simp [termSubstAtCode, functionCode,
            Semiterm.encode_eq_toNat, Semiterm.toNat, Matrix.vecToNat,
            Rew.func]
      | one =>
          simp [termSubstAtCode, functionCode,
            Semiterm.encode_eq_toNat, Semiterm.toNat, Matrix.vecToNat,
            Rew.func]
      | add =>
          simp [termSubstAtCode, functionCode, binaryVectorCode,
            Semiterm.encode_eq_toNat, Semiterm.toNat, Matrix.vecToNat,
            Matrix.vecHead, Matrix.vecTail, Rew.func]
          constructor
          · simpa only [Semiterm.encode_eq_toNat] using ih 0
          · simpa only [Semiterm.encode_eq_toNat] using ih 1
      | mul =>
          simp [termSubstAtCode, functionCode, binaryVectorCode,
            Semiterm.encode_eq_toNat, Semiterm.toNat, Matrix.vecToNat,
            Matrix.vecHead, Matrix.vecTail, Rew.func]
          constructor
          · simpa only [Semiterm.encode_eq_toNat] using ih 0
          · simpa only [Semiterm.encode_eq_toNat] using ih 1

private theorem formulaSubstAtCode_encode (t : ArithmeticSyntacticTerm) :
    ∀ (d : ℕ) (p : ArithmeticSemiproposition (d + 1)),
      formulaSubstAtCode (encode t) d (encode p) =
        encode (Rew.subst (substAtVec t d) ▹ p)
  | d, ⊤ => by
      simp [formulaSubstAtCode, Semiformula.encode_eq_toNat,
        Semiformula.toNat]
  | d, ⊥ => by
      simp [formulaSubstAtCode, Semiformula.encode_eq_toNat,
        Semiformula.toNat]
  | d, FFL.FirstOrder.Semiformula.rel r v => by
      cases r with
      | eq =>
          simp [formulaSubstAtCode, relationCode, binaryVectorCode,
            Semiformula.encode_eq_toNat, Semiformula.toNat,
            Matrix.vecToNat, Matrix.vecHead, Matrix.vecTail,
            termSubstAtCode_encode]
      | lt =>
          simp [formulaSubstAtCode, relationCode, binaryVectorCode,
            Semiformula.encode_eq_toNat, Semiformula.toNat,
            Matrix.vecToNat, Matrix.vecHead, Matrix.vecTail,
            termSubstAtCode_encode]
  | d, FFL.FirstOrder.Semiformula.nrel r v => by
      cases r with
      | eq =>
          simp [formulaSubstAtCode, relationCode, binaryVectorCode,
            Semiformula.encode_eq_toNat, Semiformula.toNat,
            Matrix.vecToNat, Matrix.vecHead, Matrix.vecTail,
            termSubstAtCode_encode]
      | lt =>
          simp [formulaSubstAtCode, relationCode, binaryVectorCode,
            Semiformula.encode_eq_toNat, Semiformula.toNat,
            Matrix.vecToNat, Matrix.vecHead, Matrix.vecTail,
            termSubstAtCode_encode]
  | d, p ⋏ q => by
      simp [formulaSubstAtCode, Semiformula.encode_eq_toNat,
        Semiformula.toNat]
      constructor
      · simpa only [Semiformula.encode_eq_toNat] using
          formulaSubstAtCode_encode t d p
      · simpa only [Semiformula.encode_eq_toNat] using
          formulaSubstAtCode_encode t d q
  | d, p ⋎ q => by
      simp [formulaSubstAtCode, Semiformula.encode_eq_toNat,
        Semiformula.toNat]
      constructor
      · simpa only [Semiformula.encode_eq_toNat] using
          formulaSubstAtCode_encode t d p
      · simpa only [Semiformula.encode_eq_toNat] using
          formulaSubstAtCode_encode t d q
  | d, ∀¹ p => by
      simp [formulaSubstAtCode, Semiformula.encode_eq_toNat,
        Semiformula.toNat, substAtVec_q]
      simpa only [Semiformula.encode_eq_toNat] using
        formulaSubstAtCode_encode t (d + 1) p
  | d, ∃¹ p => by
      simp [formulaSubstAtCode, Semiformula.encode_eq_toNat,
        Semiformula.toNat, substAtVec_q]
      simpa only [Semiformula.encode_eq_toNat] using
        formulaSubstAtCode_encode t (d + 1) p

/-- On the code of a term and the code of a formula, the numerical constructor returns
the code of Foundation's capture-avoiding one-variable substitution. -/
theorem subst1Code_encode (t : ArithmeticSyntacticTerm)
    (p : ArithmeticFormulaBody) :
    subst1Code (encode t) (encode p) =
      encode (Rew.subst ![t] ▹ p) := by
  have h := formulaSubstAtCode_encode t 0 p
  simpa [subst1Code, termCodeValid, formulaBodyCodeValid,
    substAtVec_zero] using h

theorem subst1Code_eq_substs1 {t p : ℕ}
    (ht : IsSemiterm ℒₒᵣ 0 t) (hp : IsSemiformula ℒₒᵣ 1 p) :
    subst1Code t p = substs1 ℒₒᵣ t p := by
  rcases ht.sound with ⟨u, hu⟩
  rcases hp.sound with ⟨φ, hφ⟩
  rw [← hu, ← hφ]
  calc
    subst1Code (⌜u⌝ : ℕ) (⌜φ⌝ : ℕ) =
        encode (Rew.subst ![u] ▹ φ) := by
      rw [Semiterm.quote_eq_encode_standard,
        Semiformula.quote_eq_encode_nat]
      exact subst1Code_encode u φ
    _ = (⌜Rew.subst ![u] ▹ φ⌝ : ℕ) :=
      (Semiformula.quote_eq_encode_nat _).symm
    _ = substs1 ℒₒᵣ (⌜u⌝ : ℕ) (⌜φ⌝ : ℕ) := by
      simp [substs1, Semiformula.quote_def, Semiterm.quote_def,
        Matrix.constant_eq_singleton]

/-! ## Model-internal operation and exact graph -/

/-- The model-internal total operation.  Its inputs and output are elements of
the ambient PA model, rather than external natural numbers. -/
noncomputable def subst1Value
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (t p : V) : V :=
  @ite V (IsSemiterm ℒₒᵣ 0 t ∧ IsSemiformula ℒₒᵣ 1 p)
    (Classical.propDecidable _)
    (substs1 ℒₒᵣ t p) 0

/-- Compositional arithmetic graph of `subst1Value`, with output-first
coordinates `(y,t,p)`. -/
noncomputable def subst1Graph : 𝚺₁.Semisentence 3 := .mkSigma
  “y t p.
    ((!(isSemiterm ℒₒᵣ).sigma 0 t ∧
      !(isSemiformula ℒₒᵣ).sigma 1 p ∧
      !(substs1Graph ℒₒᵣ) y t p) ∨
    ((¬!(isSemiterm ℒₒᵣ).pi 0 t ∨
      ¬!(isSemiformula ℒₒᵣ).pi 1 p) ∧ y = 0))”

theorem subst1Graph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y t p : V) :
    Semiformula.Evalb (M := V) ![y, t, p] subst1Graph.val ↔
      y = subst1Value t p := by
  by_cases ht : IsSemiterm ℒₒᵣ 0 t <;>
    by_cases hp : IsSemiformula ℒₒᵣ 1 p <;>
    simp [subst1Graph, subst1Value, ht, hp,
      HierarchySymbol.Semiformula.val_sigma, substs1.defined.iff,
      IsSemiterm.defined.iff, IsSemiformula.defined.iff]

theorem subst1Graph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (t p : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, t, p] subst1Graph.val :=
  ⟨subst1Value t p, (subst1Graph_iff _ _ _).mpr rfl⟩

theorem subst1Graph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z t p : V}
    (hy : Semiformula.Evalb (M := V) ![y, t, p] subst1Graph.val)
    (hz : Semiformula.Evalb (M := V) ![z, t, p] subst1Graph.val) :
    y = z :=
  (subst1Graph_iff y t p).mp hy |>.trans
    ((subst1Graph_iff z t p).mp hz).symm

theorem subst1Value_eq_substs1
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {t p : V} (ht : IsSemiterm ℒₒᵣ 0 t)
    (hp : IsSemiformula ℒₒᵣ 1 p) :
    subst1Value t p = substs1 ℒₒᵣ t p := by
  simp [subst1Value, ht, hp]

theorem subst1Value_isSemiformula
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {t p : V} (ht : IsSemiterm ℒₒᵣ 0 t)
    (hp : IsSemiformula ℒₒᵣ 1 p) :
    IsSemiformula ℒₒᵣ 0 (subst1Value t p) := by
  rw [subst1Value_eq_substs1 ht hp]
  exact hp.substs1 ht

theorem subst1Value_neg
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {t p : V} (ht : IsSemiterm ℒₒᵣ 0 t)
    (hp : IsSemiformula ℒₒᵣ 1 p) :
    subst1Value t (neg ℒₒᵣ p) =
      neg ℒₒᵣ (subst1Value t p) := by
  rw [subst1Value_eq_substs1 ht hp.neg,
    subst1Value_eq_substs1 ht hp]
  exact substs_neg (m := 0) hp (by simp [ht])

theorem subst1Value_nat (t p : ℕ) :
    subst1Value t p = subst1Code t p := by
  by_cases ht : IsSemiterm ℒₒᵣ 0 t
  · by_cases hp : IsSemiformula ℒₒᵣ 1 p
    · rw [subst1Value_eq_substs1 ht hp,
        ← subst1Code_eq_substs1 ht hp]
    · simp [subst1Value, subst1Code,
        termCodeValid_iff_isSemiterm, formulaBodyCodeValid_iff_isSemiformula,
        ht, hp]
  · simp [subst1Value, subst1Code,
      termCodeValid_iff_isSemiterm, ht]

theorem subst1Graph_nat_iff (y t p : ℕ) :
    Semiformula.Evalb (M := ℕ) ![y, t, p] subst1Graph.val ↔
      y = subst1Code t p := by
  rw [subst1Graph_iff, subst1Value_nat]

/-! ## Structural typing examples -/

/-- A substitution term with a free variable distinct from the free variable
in the formula body. -/
def freeVariableTerm : ArithmeticSyntacticTerm :=
  &1

/-- A one-bound-variable body that also contains free variable `&0`. -/
def freeVariableBody : ArithmeticFormulaBody :=
  “x. x = &0”

/-- Substitution replaces `x` by `&1` and retains the body's `&0`. -/
def freeVariableInstance : ArithmeticSemiproposition 0 :=
  “&1 = &0”

theorem freeVariable_structural :
    Rew.subst ![freeVariableTerm] ▹ freeVariableBody =
      freeVariableInstance := by
  simp [freeVariableTerm, freeVariableBody, freeVariableInstance]

theorem freeVariable_code :
    subst1Code (encode freeVariableTerm) (encode freeVariableBody) =
      encode freeVariableInstance := by
  rw [subst1Code_encode, freeVariable_structural]

/-- The free-variable term used to test substitution below an inner binder. -/
def nestedQuantifierTerm : ArithmeticSyntacticTerm :=
  &0

/-- In this body, `x` becomes de Bruijn index one below the quantifier for
`y`; the index zero continues to denote `y`. -/
def nestedQuantifierBody : ArithmeticFormulaBody :=
  “x. ∀ y, x = y”

/-- Capture-avoiding substitution shifts through the binder and leaves its
bound variable in place. -/
def nestedQuantifierInstance : ArithmeticSemiproposition 0 :=
  “∀ y, &0 = y”

theorem nestedQuantifier_structural :
    Rew.subst ![nestedQuantifierTerm] ▹ nestedQuantifierBody =
      nestedQuantifierInstance := by
  simp [nestedQuantifierTerm, nestedQuantifierBody,
    nestedQuantifierInstance, Rew.q_subst]

theorem nestedQuantifier_code :
    subst1Code (encode nestedQuantifierTerm)
        (encode nestedQuantifierBody) =
      encode nestedQuantifierInstance := by
  rw [subst1Code_encode, nestedQuantifier_structural]

end FailureOfComposition.NativeSubstitution
