/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NativeNumeralComparisonSeeds
import FailureOfComposition.NativeNumeralInstances

/-!
# Literal specialization of comparison seeds

Two-variable specialization first substitutes the outer variable `x`, then
`y`. The remaining helpers retain the accepted three- and four-variable
operational order. All formula identities below are identities of codes.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeNumeralComparison

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open FailureOfComposition.NativeNumeralArithmetic
open FailureOfComposition.NativeEqualityTransport

open FailureOfComposition.NativeContextSpecialization
open FailureOfComposition.NativeSubstitution
open FailureOfComposition.NativeFamilyExtraction

def instance2Code (body x y : ℕ) : ℕ :=
  subst1Code (numeralTermCode y) (nextBodyCode body x)

def specialize2Code (body Γ seed x y : ℕ) : ℕ :=
  specializeCtx Γ (nextBodyCode body x) (numeralTermCode y)
    (specializeCtx Γ body (numeralTermCode x) seed)

theorem primrec_instance2 {X : Type*} [Primcodable X] {b x y : X → ℕ}
    (hb : Primrec b) (hx : Primrec x) (hy : Primrec y) :
    Primrec (fun u => instance2Code (b u) (x u) (y u)) := by
  exact primrec₂_subst1Code.comp (primrec_numeralTermCode.comp hy) (primrec_nextBody hb hx)

theorem primrec_specialize2 {X : Type*} [Primcodable X] {b g s x y : X → ℕ}
    (hb : Primrec b) (hg : Primrec g) (hs : Primrec s) (hx : Primrec x) (hy : Primrec y) :
    Primrec (fun u => specialize2Code (b u) (g u) (s u) (x u) (y u)) := by
  exact primrec_specialize hg (primrec_nextBody hb hx) (primrec_numeralTermCode.comp hy)
    (primrec_specialize hg hb (primrec_numeralTermCode.comp hx) hs)

noncomputable def instance2Graph : 𝚺₁.Semisentence 4 := .mkSigma
  “o body x y. ∃ b, !nextBodyGraph b body x ∧
    ∃ ny, !numeralTermCodeGraph ny y ∧ !subst1Graph o ny b”

noncomputable def specialize2Graph : 𝚺₁.Semisentence 6 := .mkSigma
  “o body Γ seed x y. ∃ b, !nextBodyGraph b body x ∧
    ∃ nx, !numeralTermCodeGraph nx x ∧ ∃ ny, !numeralTermCodeGraph ny y ∧
    ∃ d, !specializeCtxGraph d Γ body nx seed ∧ !specializeCtxGraph o Γ b ny d”

section Internal

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

noncomputable def instance2Value (body x y : V) : V :=
  subst1Value (Arithmetic.numeral y) (nextBodyValue body x)

noncomputable def specialize2Value (body Γ seed x y : V) : V :=
  specializeCtxValue Γ (nextBodyValue body x) (Arithmetic.numeral y)
    (specializeCtxValue Γ body (Arithmetic.numeral x) seed)

@[simp] theorem instance2Graph_eval (v : Fin 4 → V) :
    instance2Graph.val.Evalb v ↔ v 0 = instance2Value (v 1) (v 2) (v 3) := by
  simp [instance2Graph, instance2Value, numeralTermCodeGraph_iff, subst1Graph_iff]

@[simp] theorem specialize2Graph_eval (v : Fin 6 → V) :
    specialize2Graph.val.Evalb v ↔
      v 0 = specialize2Value (v 1) (v 2) (v 3) (v 4) (v 5) := by
  simp [specialize2Graph, specialize2Value, numeralTermCodeGraph_iff]

private theorem first2 (phi : Bootstrapping.Semiformula V ℒₒᵣ 2) (x : V) :
    subst1Value (Arithmetic.numeral x) (^∀ phi.val) =
      ^∀ (phi.subst ![Bootstrapping.Semiterm.bvar (0 : Fin 1), typedNumeral x]).val := by
  rw [show (^∀ phi.val : V) = (∀¹ phi : Bootstrapping.Semiformula V ℒₒᵣ 1).val from rfl,
    subst1Value_typedNumeral]
  simp only [Bootstrapping.Semiformula.substs_all, Bootstrapping.Semiformula.val_all]
  congr 2
  apply congrArg (fun w : Bootstrapping.SemitermVec V ℒₒᵣ 2 1 => phi.subst w)
  funext i
  fin_cases i <;> simp [SemitermVec.q, toNumVec]

theorem instance2_typed (phi : Bootstrapping.Semiformula V ℒₒᵣ 2) (x y : V) :
    instance2Value (^∀ phi.val) x y = (phi.subst (toNumVec (k := 0) ![y, x])).val := by
  simp only [instance2Value, nextBodyValue, first2, allBodyValue_all,
    subst1Value_typedNumeral, Bootstrapping.Semiformula.substs_substs]
  congr 2
  funext i
  fin_cases i <;> simp [toNumVec]

theorem derivationOf_specialize2 (S : ArithmeticTheory) [S.Δ₁]
    (phi : Bootstrapping.Semiformula V ℒₒᵣ 2) {Γ seed x y : V}
    (hs : DerivationOf S seed (insert (^∀ (^∀ phi.val)) Γ)) :
    DerivationOf S (specialize2Value (^∀ phi.val) Γ seed x y)
      (insert (instance2Value (^∀ phi.val) x y) Γ) := by
  have h₁ := derivationOf_specializeNumeral S (u := x) hs
  rw [first2] at h₁
  have h₂ := derivationOf_specializeNumeral S (u := y) h₁
  simpa only [specialize2Value, instance2Value, nextBodyValue, first2, allBodyValue_all] using h₂

theorem ltBridgeBody_cast : (ltBridgeBodyCode : V) = ^∀ (^∀ (^∀ ((⌜ltBridgeMatrix⌝ : V)))) := by
  rw [ltBridgeBodyCode, ← Sentence.quote_eq_encode]
  simp only [ltBridgeBody, all_quote]

theorem ltBridgeSentence_literal : (⌜ltBridgeSentence⌝ : V) = ^∀ (^∀ (^∀ (^∀ ((⌜ltBridgeMatrix⌝
  : Bootstrapping.Semiformula V ℒₒᵣ 4).val)))) := by
  rw [ltBridgeSentence, ltBridgeBody, all_quote, all_quote, all_quote, all_quote, Sentence.quote_eq]

theorem nltBridgeBody_cast : (nltBridgeBodyCode : V) = ^∀ (^∀ ((⌜nltBridgeMatrix⌝ : V))) := by
  rw [nltBridgeBodyCode, ← Sentence.quote_eq_encode]
  simp only [nltBridgeBody, all_quote]

theorem nltBridgeSentence_literal : (⌜nltBridgeSentence⌝ : V) = ^∀ (^∀ (^∀ ((⌜nltBridgeMatrix⌝ :
  Bootstrapping.Semiformula V ℒₒᵣ 3).val))) := by
  rw [nltBridgeSentence, nltBridgeBody, all_quote, all_quote, all_quote, Sentence.quote_eq]

theorem neForwardBody_cast : (neForwardBodyCode : V) = ^∀ ((⌜neForwardMatrix⌝ : V)) := by
  rw [neForwardBodyCode, ← Sentence.quote_eq_encode]
  simp only [neForwardBody, all_quote]

theorem neForwardSentence_literal : (⌜neForwardSentence⌝ : V) = ^∀ (^∀ ((⌜neForwardMatrix⌝ :
  Bootstrapping.Semiformula V ℒₒᵣ 2).val)) := by
  rw [neForwardSentence, neForwardBody, all_quote, all_quote, Sentence.quote_eq]

theorem neReverseBody_cast : (neReverseBodyCode : V) = ^∀ ((⌜neReverseMatrix⌝ : V)) := by
  rw [neReverseBodyCode, ← Sentence.quote_eq_encode]
  simp only [neReverseBody, all_quote]

theorem neReverseSentence_literal : (⌜neReverseSentence⌝ : V) = ^∀ (^∀ ((⌜neReverseMatrix⌝ :
  Bootstrapping.Semiformula V ℒₒᵣ 2).val)) := by
  rw [neReverseSentence, neReverseBody, all_quote, all_quote, Sentence.quote_eq]

theorem ltBridge_instance (x y z w : V) :
    instance4Value (ltBridgeBodyCode : V) x y z w =
      imp ℒₒᵣ (qqEQ (qqAdd (Arithmetic.numeral y) (Arithmetic.numeral x)) (Arithmetic.numeral z))
        (imp ℒₒᵣ (qqEQ (qqAdd (Arithmetic.numeral z) (Arithmetic.numeral 1)) (Arithmetic.numeral w))
          (ltTarget x w)) := by
  rw [ltBridgeBody_cast, Sentence.quote_eq ltBridgeMatrix, instance4_typed]
  simp [ltBridgeMatrix, Sentence.typed_quote_def, toNumVec, ltTarget]

theorem nltBridge_instance (x y z : V) :
    instance3Value (nltBridgeBodyCode : V) x y z =
      imp ℒₒᵣ (qqEQ (qqAdd (Arithmetic.numeral y) (Arithmetic.numeral x)) (Arithmetic.numeral z))
        (nltTarget z x) := by
  rw [nltBridgeBody_cast, Sentence.quote_eq nltBridgeMatrix, instance3_typed]
  simp [nltBridgeMatrix, Sentence.typed_quote_def, toNumVec, nltTarget]

theorem neForward_instance (x y : V) :
    instance2Value (neForwardBodyCode : V) x y = imp ℒₒᵣ (ltTarget x y) (neTarget x y) := by
  rw [neForwardBody_cast, Sentence.quote_eq neForwardMatrix, instance2_typed]
  simp [neForwardMatrix, Sentence.typed_quote_def, toNumVec, ltTarget, neTarget]

theorem neReverse_instance (x y : V) :
    instance2Value (neReverseBodyCode : V) x y = imp ℒₒᵣ (ltTarget y x) (neTarget x y) := by
  rw [neReverseBody_cast, Sentence.quote_eq neReverseMatrix, instance2_typed]
  simp [neReverseMatrix, Sentence.typed_quote_def, toNumVec, ltTarget, neTarget]

end Internal

theorem instance2Value_nat (body x y : ℕ) :
    instance2Value body x y = instance2Code body x y := by
  simp [instance2Value, instance2Code, numeralTermCodeValue_nat,
    nextBodyValue_nat, subst1Value_nat]

theorem specialize2Value_nat (body Γ seed x y : ℕ) :
    specialize2Value body Γ seed x y = specialize2Code body Γ seed x y := by
  simp [specialize2Value, specialize2Code, numeralTermCodeValue_nat,
    nextBodyValue_nat, specializeCtxValue_nat]

end FailureOfComposition.NativeNumeralComparison
