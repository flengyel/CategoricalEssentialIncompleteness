/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeFamilyNumeralInstances

/-!
# Atomic equations for native numeral arithmetic

Numeral-arithmetic proof functions must conclude literal equations, rather
than equality of program indices. Here `addEq` and `mulEq` name those atomic
formula codes. Their executable counterparts use the pinned ordered-ring
encoding: function tag 2, relation tag 0, and the vector with left operand
first. Numerals retain the distinct zero and one constants; only positive
numerals satisfy the literal successor identity.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeNumeralArithmetic

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open FailureOfComposition.NativeEqualityTransport

-- Give this layer its own explicit model weakening, rather than inheriting
-- a private model instance from the earlier family-formula module.
private instance (priority := 2000) {V : Type*} [h : ORingStructure V] : Nonempty V :=
  ⟨@Zero.zero V h.toZero⟩

private noncomputable instance (priority := 2000) {V : Type*} [ORingStructure V]
    [hPA : V↓[ℒₒᵣ] ⊧* 𝗣𝗔] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ :=
  @models_of_subtheory ℒₒᵣ 𝗜𝚺₁ 𝗣𝗔 V ⟨(Zero.zero : V)⟩ _ inferInstance hPA

def binaryVectorCode (a b : ℕ) : ℕ := Nat.pair a (Nat.pair b 0 + 1) + 1

def binaryFunctionCode (symbol a b : ℕ) : ℕ :=
  qqFuncN 2 symbol (binaryVectorCode a b)

def addTermCode (a b : ℕ) : ℕ := binaryFunctionCode addIndex a b

def mulTermCode (a b : ℕ) : ℕ := binaryFunctionCode mulIndex a b

def atomicEqCode (a b : ℕ) : ℕ :=
  Nat.pair 0 (Nat.pair 2 (Nat.pair eqIndex (binaryVectorCode a b))) + 1

def addEqCode (n m : ℕ) : ℕ :=
  atomicEqCode (addTermCode (numeralTermCode n) (numeralTermCode m)) (numeralTermCode (n + m))

def mulEqCode (n m : ℕ) : ℕ :=
  atomicEqCode (mulTermCode (numeralTermCode n) (numeralTermCode m)) (numeralTermCode (n * m))

theorem primrec₂_binaryVectorCode : Primrec₂ binaryVectorCode := by
  exact (Primrec.succ.comp (Primrec₂.natPair.comp Primrec.fst
    (Primrec.succ.comp (Primrec₂.natPair.comp Primrec.snd (Primrec.const 0))))).to₂

theorem primrec₂_binaryFunctionCode (symbol : ℕ) : Primrec₂ (binaryFunctionCode symbol) := by
  exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2)
    (Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec₂.natPair.comp (Primrec.const symbol) primrec₂_binaryVectorCode)))).to₂

theorem primrec₂_addTermCode : Primrec₂ addTermCode := primrec₂_binaryFunctionCode _

theorem primrec₂_mulTermCode : Primrec₂ mulTermCode := primrec₂_binaryFunctionCode _

theorem primrec₂_atomicEqCode : Primrec₂ atomicEqCode := by
  exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 0)
    (Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec₂.natPair.comp (Primrec.const eqIndex) primrec₂_binaryVectorCode)))).to₂

theorem primrec₂_addEqCode : Primrec₂ addEqCode := by
  exact primrec₂_atomicEqCode.comp
    (primrec₂_addTermCode.comp (primrec_numeralTermCode.comp Primrec.fst)
      (primrec_numeralTermCode.comp Primrec.snd))
    (primrec_numeralTermCode.comp (Primrec.nat_add.comp Primrec.fst Primrec.snd))

theorem primrec₂_mulEqCode : Primrec₂ mulEqCode := by
  exact primrec₂_atomicEqCode.comp
    (primrec₂_mulTermCode.comp (primrec_numeralTermCode.comp Primrec.fst)
      (primrec_numeralTermCode.comp Primrec.snd))
    (primrec_numeralTermCode.comp (Primrec.nat_mul.comp Primrec.fst Primrec.snd))

section Internal

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

noncomputable def addEq (n m : V) : V :=
  qqEQ (qqAdd (Arithmetic.numeral n) (Arithmetic.numeral m)) (Arithmetic.numeral (n + m))

noncomputable def mulEq (n m : V) : V :=
  qqEQ (qqMul (Arithmetic.numeral n) (Arithmetic.numeral m)) (Arithmetic.numeral (n * m))

noncomputable def addEqGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “c n m. ∃ nn, !numeralTermCodeGraph nn n ∧
    ∃ nm, !numeralTermCodeGraph nm m ∧
    ∃ ns, !numeralTermCodeGraph ns (n + m) ∧
    ∃ t, !qqAddGraph t nn nm ∧ !qqEQDef c t ns”

noncomputable def mulEqGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “c n m. ∃ nn, !numeralTermCodeGraph nn n ∧
    ∃ nm, !numeralTermCodeGraph nm m ∧
    ∃ ns, !numeralTermCodeGraph ns (n * m) ∧
    ∃ t, !qqMulGraph t nn nm ∧ !qqEQDef c t ns”

theorem addEqGraph_iff (c n m : V) :
    addEqGraph.val.Evalb ![c, n, m] ↔ c = addEq n m := by
  simp [addEqGraph, addEq, numeralTermCodeGraph_iff,
    qqAdd_defined.iff, qqEQ_defined.iff]

theorem mulEqGraph_iff (c n m : V) :
    mulEqGraph.val.Evalb ![c, n, m] ↔ c = mulEq n m := by
  simp [mulEqGraph, mulEq, numeralTermCodeGraph_iff,
    qqMul_defined.iff, qqEQ_defined.iff]

theorem addEq_isFormula (n m : V) : IsFormula ℒₒᵣ (addEq n m) := by
  simp [addEq, qqEQ, qqAdd]

theorem mulEq_isFormula (n m : V) : IsFormula ℒₒᵣ (mulEq n m) := by
  simp [mulEq, qqEQ, qqMul]

theorem addTermCode_cast (a b : ℕ) :
    (addTermCode a b : V) = qqAdd (a : V) (b : V) := by
  simp [addTermCode, binaryFunctionCode, binaryVectorCode, qqFuncN, qqAdd,
    qqFunc, nat_cast_pair, ← nat_pair_eq, adjoin_def]

theorem mulTermCode_cast (a b : ℕ) :
    (mulTermCode a b : V) = qqMul (a : V) (b : V) := by
  simp [mulTermCode, binaryFunctionCode, binaryVectorCode, qqFuncN, qqMul,
    qqFunc, nat_cast_pair, ← nat_pair_eq, adjoin_def]

theorem atomicEqCode_cast (a b : ℕ) :
    (atomicEqCode a b : V) = qqEQ (a : V) (b : V) := by
  simp [atomicEqCode, binaryVectorCode, qqEQ, qqRel, nat_cast_pair,
    ← nat_pair_eq, adjoin_def]

end Internal

theorem addTermCode_nat (a b : ℕ) : qqAdd a b = addTermCode a b := by
  simpa using (addTermCode_cast (V := ℕ) a b).symm

theorem mulTermCode_nat (a b : ℕ) : qqMul a b = mulTermCode a b := by
  simpa using (mulTermCode_cast (V := ℕ) a b).symm

theorem atomicEqCode_nat (a b : ℕ) : qqEQ a b = atomicEqCode a b := by
  simpa using (atomicEqCode_cast (V := ℕ) a b).symm

theorem addEq_nat (n m : ℕ) : addEq n m = addEqCode n m := by
  simp only [addEq, addEqCode, numeralTermCodeValue_nat, addTermCode_nat, atomicEqCode_nat]

theorem mulEq_nat (n m : ℕ) : mulEq n m = mulEqCode n m := by
  simp only [mulEq, mulEqCode, numeralTermCodeValue_nat, mulTermCode_nat, atomicEqCode_nat]

theorem addTermCode_valid {a b : ℕ}
    (ha : FailureOfComposition.NativeSubstitution.termCodeValid a = true)
    (hb : FailureOfComposition.NativeSubstitution.termCodeValid b = true) :
    FailureOfComposition.NativeSubstitution.termCodeValid (addTermCode a b) = true := by
  rw [FailureOfComposition.NativeSubstitution.termCodeValid_iff_isSemiterm] at ha hb ⊢
  rw [← addTermCode_nat]
  simp [qqAdd, ha, hb]
  simpa using (LOR_func_addIndex (V := ℕ))

theorem mulTermCode_valid {a b : ℕ}
    (ha : FailureOfComposition.NativeSubstitution.termCodeValid a = true)
    (hb : FailureOfComposition.NativeSubstitution.termCodeValid b = true) :
    FailureOfComposition.NativeSubstitution.termCodeValid (mulTermCode a b) = true := by
  rw [FailureOfComposition.NativeSubstitution.termCodeValid_iff_isSemiterm] at ha hb ⊢
  rw [← mulTermCode_nat]
  simp [qqMul, ha, hb]
  simpa using (LOR_func_mulIndex (V := ℕ))

theorem addEqCode_encode (n m : ℕ) :
    addEqCode n m = encode (“↑n + ↑m = ↑(n + m)” : ArithmeticSentence) := by
  have h : (⌜(“↑n + ↑m = ↑(n + m)” : ArithmeticSentence)⌝ : ℕ) = addEq n m := by
    change (⌜(“↑n + ↑m = ↑(n + m)” : ArithmeticSentence)⌝ :
      Bootstrapping.Semiformula ℕ ℒₒᵣ 0).val = _
    simp [Sentence.typed_quote_def, addEq]
  simpa only [Sentence.quote_eq_encode_nat, addEq_nat] using h.symm

theorem mulEqCode_encode (n m : ℕ) :
    mulEqCode n m = encode (“↑n * ↑m = ↑(n * m)” : ArithmeticSentence) := by
  have h : (⌜(“↑n * ↑m = ↑(n * m)” : ArithmeticSentence)⌝ : ℕ) = mulEq n m := by
    change (⌜(“↑n * ↑m = ↑(n * m)” : ArithmeticSentence)⌝ :
      Bootstrapping.Semiformula ℕ ℒₒᵣ 0).val = _
    simp [Sentence.typed_quote_def, mulEq]
  simpa only [Sentence.quote_eq_encode_nat, mulEq_nat] using h.symm

end FailureOfComposition.NativeNumeralArithmetic
