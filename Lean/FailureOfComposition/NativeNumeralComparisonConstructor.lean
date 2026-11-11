/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeNumeralComparisonInstances
public import FailureOfComposition.NativeNumeralPR

/-!
# Explicit numeral comparison proof functions

The common runtime tuple is `(seeds, ((Gamma,n),m))`, where `seeds` is
`(((r0,z1),(refl,as)),((ltBridge,nltBridge),(neForward,neReverse)))`.
Thus every constructor has eleven ordinary numerical inputs. Seed codes and
context codes may be malformed: computation remains total on those inputs.
The truncated differences specify the actual addition proofs used as premises.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeNumeralComparison

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open FailureOfComposition.NativeNumeralArithmetic
open FailureOfComposition.NativeEqualityTransport

open FailureOfComposition.NativeContextSpecialization
open FailureOfComposition.NativeFamilyExtraction

abbrev Seeds8 (X : Type*) := Seeds4 X × Seeds4 X

abbrev Args (X : Type*) := Seeds8 X × ((X × X) × X)

def eqCode (_r0 _z1 refl _as _ltBridge _nltBridge _neForward _neReverse Γ n _m : ℕ) : ℕ :=
  specializeCtx Γ reflBodyCode (numeralTermCode n) refl

def eqPacked (p : Args ℕ) : ℕ :=
  eqCode p.1.1.1.1 p.1.1.1.2 p.1.1.2.1 p.1.1.2.2 p.1.2.1.1 p.1.2.1.2 p.1.2.2.1 p.1.2.2.2 p.2.1.1
    p.2.1.2 p.2.2

def ltCode (r0 z1 refl as ltBridge _nltBridge _neForward _neReverse Γ n m : ℕ) : ℕ :=
  let d := m - (n + 1)
  let c := instance4Code ltBridgeBodyCode n d (d + n) m
  let e := specialize4Code ltBridgeBodyCode Γ ltBridge n d (d + n) m
  applyCtxCode Γ (consequentCode c)
    (applyCtxCode Γ c e (addCtx r0 z1 refl as Γ d n))
    (addCtx r0 z1 refl as Γ (d + n) 1)

def ltPacked (p : Args ℕ) : ℕ :=
  ltCode p.1.1.1.1 p.1.1.1.2 p.1.1.2.1 p.1.1.2.2 p.1.2.1.1 p.1.2.1.2 p.1.2.2.1 p.1.2.2.2 p.2.1.1
    p.2.1.2 p.2.2

def nltCode (r0 z1 refl as _ltBridge nltBridge _neForward _neReverse Γ n m : ℕ) : ℕ :=
  let d := n - m
  let c := instance3Code nltBridgeBodyCode m d n
  applyCtxCode Γ c (specialize3Code nltBridgeBodyCode Γ nltBridge m d n)
    (addCtx r0 z1 refl as Γ d m)

def nltPacked (p : Args ℕ) : ℕ :=
  nltCode p.1.1.1.1 p.1.1.1.2 p.1.1.2.1 p.1.1.2.2 p.1.2.1.1 p.1.2.1.2 p.1.2.2.1 p.1.2.2.2
    p.2.1.1 p.2.1.2 p.2.2

def neCode (r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : ℕ) : ℕ :=
  if n < m then
    applyCtxCode Γ (instance2Code neForwardBodyCode n m)
      (specialize2Code neForwardBodyCode Γ neForward n m)
      (ltCode r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m)
  else
    applyCtxCode Γ (instance2Code neReverseBodyCode n m)
      (specialize2Code neReverseBodyCode Γ neReverse n m)
      (ltCode r0 z1 refl as ltBridge nltBridge neForward neReverse Γ m n)

def nePacked (p : Args ℕ) : ℕ :=
  neCode p.1.1.1.1 p.1.1.1.2 p.1.1.2.1 p.1.1.2.2 p.1.2.1.1 p.1.2.1.2 p.1.2.2.1 p.1.2.2.2 p.2.1.1
    p.2.1.2 p.2.2

def signedEqCode (r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : ℕ) : ℕ :=
  if n = m then eqCode r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m
  else neCode r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m

def signedEqPacked (p : Args ℕ) : ℕ :=
  signedEqCode p.1.1.1.1 p.1.1.1.2 p.1.1.2.1 p.1.1.2.2 p.1.2.1.1 p.1.2.1.2 p.1.2.2.1 p.1.2.2.2
    p.2.1.1 p.2.1.2 p.2.2

def signedLtCode (r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : ℕ) : ℕ :=
  if n < m then ltCode r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m
  else nltCode r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m

def signedLtPacked (p : Args ℕ) : ℕ :=
  signedLtCode p.1.1.1.1 p.1.1.1.2 p.1.1.2.1 p.1.1.2.2 p.1.2.1.1 p.1.2.1.2 p.1.2.2.1 p.1.2.2.2
    p.2.1.1 p.2.1.2 p.2.2

theorem primrec_eqCode {X : Type*} [Primcodable X]
    {r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : X → ℕ}
    (_h0 : Primrec r0) (_h1 : Primrec z1) (hr : Primrec refl) (_ha : Primrec as)
    (_hl : Primrec ltBridge) (_hnl : Primrec nltBridge)
    (_hf : Primrec neForward) (_hv : Primrec neReverse)
    (hg : Primrec Γ) (hn : Primrec n) (_hm : Primrec m) :
    Primrec (fun u => eqCode (r0 u) (z1 u) (refl u) (as u) (ltBridge u) (nltBridge u) (neForward
      u) (neReverse u) (Γ u) (n u) (m u)) := by
  exact primrec_specialize hg (Primrec.const reflBodyCode) (primrec_numeralTermCode.comp hn) hr

theorem primrec_eqPacked : Primrec eqPacked := by
  exact primrec_eqCode
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id)))
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id)))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.id))

theorem primrec_ltCode {X : Type*} [Primcodable X]
    {r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : X → ℕ}
    (h0 : Primrec r0) (h1 : Primrec z1) (hr : Primrec refl) (ha : Primrec as)
    (hl : Primrec ltBridge) (_hnl : Primrec nltBridge)
    (_hf : Primrec neForward) (_hv : Primrec neReverse)
    (hg : Primrec Γ) (hn : Primrec n) (hm : Primrec m) :
    Primrec (fun u => ltCode (r0 u) (z1 u) (refl u) (as u) (ltBridge u) (nltBridge u) (neForward
      u) (neReverse u) (Γ u) (n u) (m u)) := by
  have hd := Primrec.nat_sub.comp hm (Primrec.succ.comp hn)
  have hz := Primrec.nat_add.comp hd hn
  have hc := primrec_instance4 (Primrec.const ltBridgeBodyCode) hn hd hz hm
  have he := primrec_specialize4 (Primrec.const ltBridgeBodyCode) hg hl hn hd hz hm
  exact primrec_apply hg (primrec_consequentCode.comp hc)
    (primrec_apply hg hc he (primrec_addCtx h0 h1 hr ha hg hd hn))
    (primrec_addCtx h0 h1 hr ha hg hz (Primrec.const 1))

theorem primrec_ltPacked : Primrec ltPacked := by
  exact primrec_ltCode
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id)))
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id)))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.id))

theorem primrec_nltCode {X : Type*} [Primcodable X]
    {r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : X → ℕ}
    (h0 : Primrec r0) (h1 : Primrec z1) (hr : Primrec refl) (ha : Primrec as)
    (_hl : Primrec ltBridge) (hnl : Primrec nltBridge)
    (_hf : Primrec neForward) (_hv : Primrec neReverse)
    (hg : Primrec Γ) (hn : Primrec n) (hm : Primrec m) :
    Primrec (fun u => nltCode (r0 u) (z1 u) (refl u) (as u) (ltBridge u) (nltBridge u)
      (neForward u) (neReverse u) (Γ u) (n u) (m u)) := by
  have hd := Primrec.nat_sub.comp hn hm
  have hc := primrec_instance3 (Primrec.const nltBridgeBodyCode) hm hd hn
  exact primrec_apply hg hc
    (primrec_specialize3 (Primrec.const nltBridgeBodyCode) hg hnl hm hd hn)
    (primrec_addCtx h0 h1 hr ha hg hd hm)

theorem primrec_nltPacked : Primrec nltPacked := by
  exact primrec_nltCode
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id)))
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id)))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.id))

theorem primrec_neCode {X : Type*} [Primcodable X]
    {r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : X → ℕ}
    (h0 : Primrec r0) (h1 : Primrec z1) (hr : Primrec refl) (ha : Primrec as)
    (hl : Primrec ltBridge) (hnl : Primrec nltBridge)
    (hf : Primrec neForward) (hv : Primrec neReverse)
    (hg : Primrec Γ) (hn : Primrec n) (hm : Primrec m) :
    Primrec (fun u => neCode (r0 u) (z1 u) (refl u) (as u) (ltBridge u) (nltBridge u) (neForward
      u) (neReverse u) (Γ u) (n u) (m u)) := by
  exact Primrec.ite (Primrec.nat_lt.comp hn hm)
    (primrec_apply hg (primrec_instance2 (Primrec.const neForwardBodyCode) hn hm)
      (primrec_specialize2 (Primrec.const neForwardBodyCode) hg hf hn hm)
      (primrec_ltCode h0 h1 hr ha hl hnl hf hv hg hn hm))
    (primrec_apply hg (primrec_instance2 (Primrec.const neReverseBodyCode) hn hm)
      (primrec_specialize2 (Primrec.const neReverseBodyCode) hg hv hn hm)
      (primrec_ltCode h0 h1 hr ha hl hnl hf hv hg hm hn))

theorem primrec_nePacked : Primrec nePacked := by
  exact primrec_neCode
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id)))
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id)))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.id))

theorem primrec_signedEqCode {X : Type*} [Primcodable X]
    {r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : X → ℕ}
    (h0 : Primrec r0) (h1 : Primrec z1) (hr : Primrec refl) (ha : Primrec as)
    (hl : Primrec ltBridge) (hnl : Primrec nltBridge)
    (hf : Primrec neForward) (hv : Primrec neReverse)
    (hg : Primrec Γ) (hn : Primrec n) (hm : Primrec m) :
    Primrec (fun u => signedEqCode (r0 u) (z1 u) (refl u) (as u) (ltBridge u) (nltBridge u)
      (neForward u) (neReverse u) (Γ u) (n u) (m u)) := by
  exact Primrec.ite (Primrec.eq.comp hn hm)
    (primrec_eqCode h0 h1 hr ha hl hnl hf hv hg hn hm)
    (primrec_neCode h0 h1 hr ha hl hnl hf hv hg hn hm)

theorem primrec_signedEqPacked : Primrec signedEqPacked := by
  exact primrec_signedEqCode
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id)))
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id)))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.id))

theorem primrec_signedLtCode {X : Type*} [Primcodable X]
    {r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : X → ℕ}
    (h0 : Primrec r0) (h1 : Primrec z1) (hr : Primrec refl) (ha : Primrec as)
    (hl : Primrec ltBridge) (hnl : Primrec nltBridge)
    (hf : Primrec neForward) (hv : Primrec neReverse)
    (hg : Primrec Γ) (hn : Primrec n) (hm : Primrec m) :
    Primrec (fun u => signedLtCode (r0 u) (z1 u) (refl u) (as u) (ltBridge u) (nltBridge u)
      (neForward u) (neReverse u) (Γ u) (n u) (m u)) := by
  exact Primrec.ite (Primrec.nat_lt.comp hn hm)
    (primrec_ltCode h0 h1 hr ha hl hnl hf hv hg hn hm)
    (primrec_nltCode h0 h1 hr ha hl hnl hf hv hg hn hm)

theorem primrec_signedLtPacked : Primrec signedLtPacked := by
  exact primrec_signedLtCode
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id)))
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id)))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.id))

end FailureOfComposition.NativeNumeralComparison
