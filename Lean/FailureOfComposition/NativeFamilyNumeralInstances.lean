/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeFamilyInstances
public import FailureOfComposition.NativeFamilyNat
public import FailureOfComposition.NativeFamilyPR

/-!
# Total unary and binary numeral-instance constructors

The numerical input `code` is supplied explicitly. Binary coordinates are
`(u,y)`; the constructor first specializes `y` under the remaining `u` binder,
then specializes `u`. The internal coding identities apply to arbitrary model
elements, including nonstandard numerals.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeFamilyExtraction

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open FailureOfComposition.NativeContextSpecialization
open FailureOfComposition.NativeSubstitution
open FailureOfComposition.NativeEqualityTransport

def unaryInstanceCode (code u : ℕ) : ℕ := subst1Code (numeralTermCode u) code

def binaryInstanceCode (code u y : ℕ) : ℕ :=
  subst1Code (numeralTermCode u)
    (allBodyCode (subst1Code (numeralTermCode y) (formulaAllCode code)))

theorem primrec₂_unaryInstanceCode : Primrec₂ unaryInstanceCode := by
  exact primrec₂_subst1Code.comp (primrec_numeralTermCode.comp Primrec.snd) Primrec.fst

theorem primrec_binaryInstanceCode :
    Primrec (fun z : (ℕ × ℕ) × ℕ => binaryInstanceCode z.1.1 z.1.2 z.2) := by
  have hc := Primrec.fst.comp (Primrec.fst : Primrec (fun z : (ℕ × ℕ) × ℕ => z.1))
  have hu := primrec_numeralTermCode.comp (Primrec.snd.comp
    (Primrec.fst : Primrec (fun z : (ℕ × ℕ) × ℕ => z.1)))
  have hy := primrec_numeralTermCode.comp (Primrec.snd : Primrec (fun z : (ℕ × ℕ) × ℕ => z.2))
  exact primrec₂_subst1Code.comp hu (primrec_allBodyCode.comp
    (primrec₂_subst1Code.comp hy (primrec_formulaAllCode.comp hc)))

section Internal

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

noncomputable def unaryInstanceValue (code u : V) : V :=
  subst1Value (Arithmetic.numeral u) code

noncomputable def binaryInstanceValue (code u y : V) : V :=
  subst1Value (Arithmetic.numeral u)
    (sndIdx (subst1Value (Arithmetic.numeral y) (^∀ code)))

noncomputable def unaryInstanceGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “a code u. ∃ nu, !numeralTermCodeGraph nu u ∧ !subst1Graph a nu code”

noncomputable def binaryInstanceGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “a code u y. ∃ ny, !numeralTermCodeGraph ny y ∧
    ∃ nu, !numeralTermCodeGraph nu u ∧ ∃ b, !qqAllDef b code ∧
    ∃ s, !subst1Graph s ny b ∧ ∃ t, !sndIdxDef t s ∧ !subst1Graph a nu t”

theorem unaryInstanceGraph_iff (a code u : V) :
    unaryInstanceGraph.val.Evalb ![a, code, u] ↔ a = unaryInstanceValue code u := by
  simp [unaryInstanceGraph, unaryInstanceValue, numeralTermCodeGraph_iff, subst1Graph_iff]

theorem binaryInstanceGraph_iff (a code u y : V) :
    binaryInstanceGraph.val.Evalb ![a, code, u, y] ↔ a = binaryInstanceValue code u y := by
  simp [binaryInstanceGraph, binaryInstanceValue, numeralTermCodeGraph_iff, subst1Graph_iff]

theorem unaryInstanceGraph_existsUnique (code u : V) :
    ∃! a : V, unaryInstanceGraph.val.Evalb ![a, code, u] := by
  simp only [unaryInstanceGraph_iff]
  exact existsUnique_eq

theorem binaryInstanceGraph_existsUnique (code u y : V) :
    ∃! a : V, binaryInstanceGraph.val.Evalb ![a, code, u, y] := by
  simp only [binaryInstanceGraph_iff]
  exact existsUnique_eq

theorem unaryInstance_literal (phi : ArithmeticSemisentence 1) (u : V) :
    unaryInstanceValue (⌜phi⌝ : V) u = instanceValue phi ![u] := by
  rw [unaryInstanceValue, subst1Value_eq_substs1 (by simp) (by simp)]
  rfl

theorem binaryInstance_literal (phi : ArithmeticSemisentence 2) (u y : V) :
    binaryInstanceValue (⌜phi⌝ : V) u y = instanceValue phi ![u, y] := by
  let q : Bootstrapping.Semiformula V ℒₒᵣ 2 := ⌜phi⌝
  let b : Bootstrapping.Semiformula V ℒₒᵣ 1 :=
    q.subst ![Bootstrapping.Semiterm.bvar 0, typedNumeral y]
  have first : subst1Value (Arithmetic.numeral y) (^∀ q.val) = ^∀ b.val := by
    rw [show (^∀ q.val : V) = (∀¹ q : Bootstrapping.Semiformula V ℒₒᵣ 1).val from rfl,
      subst1Value_typedNumeral]
    rw [Bootstrapping.Semiformula.substs_all]
    simp only [Bootstrapping.Semiformula.val_all]
    apply congrArg (fun w : Bootstrapping.SemitermVec V ℒₒᵣ 2 1 => ^∀ (q.subst w).val)
    funext i
    fin_cases i <;> simp [SemitermVec.q, toNumVec]
  change subst1Value (Arithmetic.numeral u)
    (sndIdx (subst1Value (Arithmetic.numeral y) (^∀ q.val))) = _
  rw [first, allBodyValue_all]
  rw [subst1Value_typedNumeral]
  dsimp only [b]
  rw [Bootstrapping.Semiformula.substs_substs]
  change (q.subst _).val = (q.subst (toNumVec (k := 0) ![u, y])).val
  congr 2
  funext i
  fin_cases i <;> simp [toNumVec]

end Internal

theorem unaryInstanceGraph_nat_iff (a code u : ℕ) :
    unaryInstanceGraph.val.Evalb ![a, code, u] ↔ a = unaryInstanceCode code u := by
  rw [unaryInstanceGraph_iff]
  simp only [unaryInstanceValue, numeralTermCodeValue_nat, subst1Value_nat, unaryInstanceCode]

theorem binaryInstanceGraph_nat_iff (a code u y : ℕ) :
    binaryInstanceGraph.val.Evalb ![a, code, u, y] ↔ a = binaryInstanceCode code u y := by
  rw [binaryInstanceGraph_iff]
  simp only [binaryInstanceValue, numeralTermCodeValue_nat, subst1Value_nat,
    allBodyValue_nat, binaryInstanceCode, qqAll, formulaAllCode, nat_pair_eq]
  rfl

theorem unaryInstanceCode_encode (phi : ArithmeticSemisentence 1) (u : ℕ) :
    unaryInstanceCode (Encodable.encode phi) u =
      Encodable.encode (phi/[(↑u : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) := by
  have h := unaryInstance_literal (V := ℕ) phi u
  simpa [unaryInstanceValue, numeralTermCodeValue_nat, subst1Value_nat,
    unaryInstanceCode, Sentence.quote_eq_encode_nat, instanceValue_nat,
    Matrix.fun_eq_vec_one] using h

theorem binaryInstanceCode_encode (phi : ArithmeticSemisentence 2) (u y : ℕ) :
    binaryInstanceCode (Encodable.encode phi) u y =
      Encodable.encode (phi/[(↑u : ArithmeticSemiterm Empty 0), ↑y] : ArithmeticSentence) := by
  have h := binaryInstance_literal (V := ℕ) phi u y
  have hg := (binaryInstanceGraph_nat_iff (binaryInstanceValue (⌜phi⌝ : ℕ) u y)
    (⌜phi⌝ : ℕ) u y).mp ((binaryInstanceGraph_iff _ _ _ _).mpr rfl)
  rw [h, instanceValue_nat] at hg
  simpa [Sentence.quote_eq_encode_nat, Matrix.fun_eq_vec_two] using hg.symm

end FailureOfComposition.NativeFamilyExtraction
