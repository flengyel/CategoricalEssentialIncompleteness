/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeNumeralConstructor

/-!
# Joint primitive recursiveness of numeral proof functions

The proofs compose the accepted numerical constructors and ordinary primitive
recursion. Every seed code and the common context remain varying inputs.
The multiplication step invokes the proved addition function at its actual
arguments, rather than choosing a proof of the needed equation.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeNumeralArithmetic

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.NativeEqualityTransport
open FailureOfComposition.NativeFamilyExtraction

theorem primrec_addOne {X : Type*} [Primcodable X] {z r g n : X → ℕ}
    (hz : Primrec z) (hr : Primrec r) (hg : Primrec g) (hn : Primrec n) :
    Primrec (fun u => addOneCode (z u) (r u) (g u) (n u)) := by
  exact Primrec.ite (Primrec.eq.comp hn (Primrec.const 0)) hz
    (primrec_specialize hg (Primrec.const reflBodyCode)
      (primrec₂_addTermCode.comp (primrec_numeralTermCode.comp hn)
        (Primrec.const Arithmetic.one)) hr)

theorem primrec_addPositive {X : Type*} [Primcodable X] {a g n k ih : X → ℕ}
    (ha : Primrec a) (hg : Primrec g) (hn : Primrec n) (hk : Primrec k) (hi : Primrec ih) :
    Primrec (fun u => addPositiveCode (a u) (g u) (n u) (k u) (ih u)) := by
  have hnk := Primrec.nat_add.comp hn hk
  exact primrec_apply hg (primrec_instance3 (Primrec.const asBodyCode) hn hk hnk)
    (primrec_specialize3 (Primrec.const asBodyCode) hg ha hn hk hnk) hi

theorem primrec_addCtx {X : Type*} [Primcodable X] {r0 z1 refl as g n m : X → ℕ}
    (h0 : Primrec r0) (h1 : Primrec z1) (hr : Primrec refl) (ha : Primrec as)
    (hg : Primrec g) (hn : Primrec n) (hm : Primrec m) :
    Primrec (fun u => addCtx (r0 u) (z1 u) (refl u) (as u) (g u) (n u) (m u)) := by
  have hb := primrec_specialize hg (Primrec.const r0BodyCode) (primrec_numeralTermCode.comp hn) h0
  have hs : Primrec₂ (fun (u : X) (p : ℕ × ℕ) =>
      if p.1 = 0 then addOneCode (z1 u) (refl u) (g u) (n u)
      else addPositiveCode (as u) (g u) (n u) p.1 p.2) := by
    exact Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0))
      (primrec_addOne (h1.comp Primrec.fst) (hr.comp Primrec.fst)
        (hg.comp Primrec.fst) (hn.comp Primrec.fst))
      (primrec_addPositive (ha.comp Primrec.fst) (hg.comp Primrec.fst)
        (hn.comp Primrec.fst) (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  apply (Primrec.nat_rec' hm hb hs).of_eq
  intro u
  induction m u with
  | zero => rfl
  | succ k ih => simp only [addCtx, ih]

theorem primrec_mulPositive {X : Type*} [Primcodable X] {r0 z1 refl as ms g n k ih : X → ℕ}
    (h0 : Primrec r0) (h1 : Primrec z1) (hr : Primrec refl) (ha : Primrec as) (hs : Primrec ms)
    (hg : Primrec g) (hn : Primrec n) (hk : Primrec k) (hi : Primrec ih) :
    Primrec (fun u =>
      mulPositiveCode (r0 u) (z1 u) (refl u) (as u) (ms u) (g u) (n u) (k u) (ih u)) := by
  have hnk := Primrec.nat_mul.comp hn hk
  have hw := Primrec.nat_add.comp hnk hn
  have hc := primrec_instance4 (Primrec.const msBodyCode) hn hk hnk hw
  have hd := primrec_specialize4 (Primrec.const msBodyCode) hg hs hn hk hnk hw
  exact primrec_apply hg (primrec_consequentCode.comp hc) (primrec_apply hg hc hd hi)
    (primrec_addCtx h0 h1 hr ha hg hnk hn)

theorem primrec_mulCtx {X : Type*} [Primcodable X] {r0 z1 refl as m0 m1 ms g n m : X → ℕ}
    (h0 : Primrec r0) (h1 : Primrec z1) (hr : Primrec refl) (ha : Primrec as)
    (hm0 : Primrec m0) (hm1 : Primrec m1) (hs : Primrec ms)
    (hg : Primrec g) (hn : Primrec n) (hm : Primrec m) :
    Primrec (fun u =>
      mulCtx (r0 u) (z1 u) (refl u) (as u) (m0 u) (m1 u) (ms u) (g u) (n u) (m u)) := by
  have hb := primrec_specialize hg (Primrec.const m0BodyCode) (primrec_numeralTermCode.comp hn) hm0
  have hstep : Primrec₂ (fun (u : X) (p : ℕ × ℕ) =>
      if p.1 = 0 then
        FailureOfComposition.NativeContextSpecialization.specializeCtx
          (g u) m1BodyCode (numeralTermCode (n u)) (m1 u)
      else mulPositiveCode (r0 u) (z1 u) (refl u) (as u) (ms u) (g u) (n u) p.1 p.2) := by
    exact Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0))
      (primrec_specialize (hg.comp Primrec.fst) (Primrec.const m1BodyCode)
        (primrec_numeralTermCode.comp (hn.comp Primrec.fst)) (hm1.comp Primrec.fst))
      (primrec_mulPositive (h0.comp Primrec.fst) (h1.comp Primrec.fst) (hr.comp Primrec.fst)
        (ha.comp Primrec.fst) (hs.comp Primrec.fst) (hg.comp Primrec.fst)
        (hn.comp Primrec.fst) (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  apply (Primrec.nat_rec' hm hb hstep).of_eq
  intro u
  induction m u with
  | zero => rfl
  | succ k ih => simp only [mulCtx, ih]

theorem primrec_addCtxPacked : Primrec addCtxPacked := by
  exact primrec_addCtx
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)

theorem primrec_mulCtxPacked : Primrec mulCtxPacked := by
  exact primrec_mulCtx
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)

end FailureOfComposition.NativeNumeralArithmetic
