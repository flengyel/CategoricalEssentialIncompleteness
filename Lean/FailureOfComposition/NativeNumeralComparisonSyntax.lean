/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NativeNumeralSyntax

/-!
# Literal numeral comparison formulas

For a numeral value `n`, `Arithmetic.numeral n` is its term code. The four
comparison targets apply the equality or order relation to these term codes,
with the left operand first. Positive atoms have tag zero and negative atoms
have tag one. Signed targets select an atom by comparing the numeral values.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeNumeralComparison

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open FailureOfComposition.NativeNumeralArithmetic
open FailureOfComposition.NativeEqualityTransport

def relationCode (tag symbol a b : ℕ) : ℕ :=
  Nat.pair tag (Nat.pair 2 (Nat.pair symbol (binaryVectorCode a b))) + 1

theorem primrec₂_relationCode (tag symbol : ℕ) : Primrec₂ (relationCode tag symbol) := by
  exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const tag)
    (Primrec₂.natPair.comp (Primrec.const 2)
      (Primrec₂.natPair.comp (Primrec.const symbol) primrec₂_binaryVectorCode)))).to₂

def eqTargetCode (n m : ℕ) : ℕ :=
  relationCode 0 eqIndex (numeralTermCode n) (numeralTermCode m)

theorem primrec₂_eqTargetCode : Primrec₂ eqTargetCode := by
  exact (primrec₂_relationCode 0 eqIndex).comp
    (primrec_numeralTermCode.comp Primrec.fst) (primrec_numeralTermCode.comp Primrec.snd)

def neTargetCode (n m : ℕ) : ℕ :=
  relationCode 1 eqIndex (numeralTermCode n) (numeralTermCode m)

theorem primrec₂_neTargetCode : Primrec₂ neTargetCode := by
  exact (primrec₂_relationCode 1 eqIndex).comp
    (primrec_numeralTermCode.comp Primrec.fst) (primrec_numeralTermCode.comp Primrec.snd)

def ltTargetCode (n m : ℕ) : ℕ :=
  relationCode 0 ltIndex (numeralTermCode n) (numeralTermCode m)

theorem primrec₂_ltTargetCode : Primrec₂ ltTargetCode := by
  exact (primrec₂_relationCode 0 ltIndex).comp
    (primrec_numeralTermCode.comp Primrec.fst) (primrec_numeralTermCode.comp Primrec.snd)

def nltTargetCode (n m : ℕ) : ℕ :=
  relationCode 1 ltIndex (numeralTermCode n) (numeralTermCode m)

theorem primrec₂_nltTargetCode : Primrec₂ nltTargetCode := by
  exact (primrec₂_relationCode 1 ltIndex).comp
    (primrec_numeralTermCode.comp Primrec.fst) (primrec_numeralTermCode.comp Primrec.snd)

def signedEqTargetCode (n m : ℕ) : ℕ :=
  if n = m then eqTargetCode n m else neTargetCode n m

def signedLtTargetCode (n m : ℕ) : ℕ :=
  if n < m then ltTargetCode n m else nltTargetCode n m

theorem primrec₂_signedEqTargetCode : Primrec₂ signedEqTargetCode := by
  exact (Primrec.ite (Primrec.eq.comp Primrec.fst Primrec.snd)
    primrec₂_eqTargetCode primrec₂_neTargetCode).to₂

theorem primrec₂_signedLtTargetCode : Primrec₂ signedLtTargetCode := by
  exact (Primrec.ite (Primrec.nat_lt.comp Primrec.fst Primrec.snd)
    primrec₂_ltTargetCode primrec₂_nltTargetCode).to₂

section Internal

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

noncomputable def eqTarget (n m : V) : V :=
  qqEQ (Arithmetic.numeral n) (Arithmetic.numeral m)

noncomputable def eqTargetGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “c n m. ∃ nn, !numeralTermCodeGraph nn n ∧
    ∃ nm, !numeralTermCodeGraph nm m ∧ !qqEQDef c nn nm”

@[simp] theorem eqTargetGraph_eval (v : Fin 3 → V) :
    eqTargetGraph.val.Evalb v ↔ v 0 = eqTarget (v 1) (v 2) := by
  simp [eqTargetGraph, eqTarget, numeralTermCodeGraph_iff, qqEQ_defined.iff]

theorem eqTarget_isFormula (n m : V) : IsFormula ℒₒᵣ (eqTarget n m) := by
  simp [eqTarget, qqEQ]

theorem relationCode_eq_cast (a b : ℕ) :
    (relationCode 0 eqIndex a b : V) = qqEQ (a : V) (b : V) := by
  simp [relationCode, binaryVectorCode, qqEQ, qqRel, nat_cast_pair,
    ← nat_pair_eq, adjoin_def]

noncomputable def neTarget (n m : V) : V :=
  qqNEQ (Arithmetic.numeral n) (Arithmetic.numeral m)

noncomputable def neTargetGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “c n m. ∃ nn, !numeralTermCodeGraph nn n ∧
    ∃ nm, !numeralTermCodeGraph nm m ∧ !qqNEQDef c nn nm”

@[simp] theorem neTargetGraph_eval (v : Fin 3 → V) :
    neTargetGraph.val.Evalb v ↔ v 0 = neTarget (v 1) (v 2) := by
  simp [neTargetGraph, neTarget, numeralTermCodeGraph_iff, qqNEQ_defined.iff]

theorem neTarget_isFormula (n m : V) : IsFormula ℒₒᵣ (neTarget n m) := by
  simp [neTarget, qqNEQ]

theorem relationCode_ne_cast (a b : ℕ) :
    (relationCode 1 eqIndex a b : V) = qqNEQ (a : V) (b : V) := by
  simp [relationCode, binaryVectorCode, qqNEQ, qqNRel, nat_cast_pair,
    ← nat_pair_eq, adjoin_def]

noncomputable def ltTarget (n m : V) : V :=
  qqLT (Arithmetic.numeral n) (Arithmetic.numeral m)

noncomputable def ltTargetGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “c n m. ∃ nn, !numeralTermCodeGraph nn n ∧
    ∃ nm, !numeralTermCodeGraph nm m ∧ !qqLTDef c nn nm”

@[simp] theorem ltTargetGraph_eval (v : Fin 3 → V) :
    ltTargetGraph.val.Evalb v ↔ v 0 = ltTarget (v 1) (v 2) := by
  simp [ltTargetGraph, ltTarget, numeralTermCodeGraph_iff, qqLT_defined.iff]

theorem ltTarget_isFormula (n m : V) : IsFormula ℒₒᵣ (ltTarget n m) := by
  simp [ltTarget, qqLT]

theorem relationCode_lt_cast (a b : ℕ) :
    (relationCode 0 ltIndex a b : V) = qqLT (a : V) (b : V) := by
  simp [relationCode, binaryVectorCode, qqLT, qqRel, nat_cast_pair,
    ← nat_pair_eq, adjoin_def]

noncomputable def nltTarget (n m : V) : V :=
  qqNLT (Arithmetic.numeral n) (Arithmetic.numeral m)

noncomputable def nltTargetGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “c n m. ∃ nn, !numeralTermCodeGraph nn n ∧
    ∃ nm, !numeralTermCodeGraph nm m ∧ !qqNLTDef c nn nm”

@[simp] theorem nltTargetGraph_eval (v : Fin 3 → V) :
    nltTargetGraph.val.Evalb v ↔ v 0 = nltTarget (v 1) (v 2) := by
  simp [nltTargetGraph, nltTarget, numeralTermCodeGraph_iff, qqNLT_defined.iff]

theorem nltTarget_isFormula (n m : V) : IsFormula ℒₒᵣ (nltTarget n m) := by
  simp [nltTarget, qqNLT]

theorem relationCode_nlt_cast (a b : ℕ) :
    (relationCode 1 ltIndex a b : V) = qqNLT (a : V) (b : V) := by
  simp [relationCode, binaryVectorCode, qqNLT, qqNRel, nat_cast_pair,
    ← nat_pair_eq, adjoin_def]

noncomputable def signedEqTarget (n m : V) : V :=
  if n = m then eqTarget n m else neTarget n m

noncomputable def signedLtTarget (n m : V) : V :=
  if n < m then ltTarget n m else nltTarget n m

noncomputable def signedEqTargetGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “c n m. (n = m ∧ !eqTargetGraph c n m) ∨ (n ≠ m ∧ !neTargetGraph c n m)”

noncomputable def signedLtTargetGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “c n m. (n < m ∧ !ltTargetGraph c n m) ∨ (¬ (n < m) ∧ !nltTargetGraph c n m)”

@[simp] theorem signedEqTargetGraph_eval (v : Fin 3 → V) :
    signedEqTargetGraph.val.Evalb v ↔ v 0 = signedEqTarget (v 1) (v 2) := by
  by_cases h : v 1 = v 2 <;> simp [signedEqTargetGraph, signedEqTarget, h]

@[simp] theorem signedLtTargetGraph_eval (v : Fin 3 → V) :
    signedLtTargetGraph.val.Evalb v ↔ v 0 = signedLtTarget (v 1) (v 2) := by
  by_cases h : v 1 < v 2 <;> simp [signedLtTargetGraph, signedLtTarget, h]

theorem signedEqTarget_isFormula (n m : V) : IsFormula ℒₒᵣ (signedEqTarget n m) := by
  unfold signedEqTarget
  split <;> apply_rules [eqTarget_isFormula, neTarget_isFormula]

theorem signedLtTarget_isFormula (n m : V) : IsFormula ℒₒᵣ (signedLtTarget n m) := by
  unfold signedLtTarget
  split <;> apply_rules [ltTarget_isFormula, nltTarget_isFormula]

theorem neg_eqTarget (n m : V) : neg ℒₒᵣ (eqTarget n m) = neTarget n m := by
  exact neg_eq (by simp) (by simp)

theorem neg_ltTarget (n m : V) : neg ℒₒᵣ (ltTarget n m) = nltTarget n m := by
  exact neg_lt (by simp) (by simp)

theorem eqTargetGraph_total (n m : V) :
    ∃ c, eqTargetGraph.val.Evalb ![c, n, m] := by
  exact ⟨eqTarget n m, (eqTargetGraph_eval _).mpr rfl⟩

theorem eqTargetGraph_functional {a b n m : V}
    (ha : eqTargetGraph.val.Evalb ![a, n, m])
    (hb : eqTargetGraph.val.Evalb ![b, n, m]) : a = b := by
  exact ((eqTargetGraph_eval _).mp ha).trans ((eqTargetGraph_eval _).mp hb).symm

theorem neTargetGraph_total (n m : V) :
    ∃ c, neTargetGraph.val.Evalb ![c, n, m] := by
  exact ⟨neTarget n m, (neTargetGraph_eval _).mpr rfl⟩

theorem neTargetGraph_functional {a b n m : V}
    (ha : neTargetGraph.val.Evalb ![a, n, m])
    (hb : neTargetGraph.val.Evalb ![b, n, m]) : a = b := by
  exact ((neTargetGraph_eval _).mp ha).trans ((neTargetGraph_eval _).mp hb).symm

theorem ltTargetGraph_total (n m : V) :
    ∃ c, ltTargetGraph.val.Evalb ![c, n, m] := by
  exact ⟨ltTarget n m, (ltTargetGraph_eval _).mpr rfl⟩

theorem ltTargetGraph_functional {a b n m : V}
    (ha : ltTargetGraph.val.Evalb ![a, n, m])
    (hb : ltTargetGraph.val.Evalb ![b, n, m]) : a = b := by
  exact ((ltTargetGraph_eval _).mp ha).trans ((ltTargetGraph_eval _).mp hb).symm

theorem nltTargetGraph_total (n m : V) :
    ∃ c, nltTargetGraph.val.Evalb ![c, n, m] := by
  exact ⟨nltTarget n m, (nltTargetGraph_eval _).mpr rfl⟩

theorem nltTargetGraph_functional {a b n m : V}
    (ha : nltTargetGraph.val.Evalb ![a, n, m])
    (hb : nltTargetGraph.val.Evalb ![b, n, m]) : a = b := by
  exact ((nltTargetGraph_eval _).mp ha).trans ((nltTargetGraph_eval _).mp hb).symm

theorem signedEqTargetGraph_total (n m : V) :
    ∃ c, signedEqTargetGraph.val.Evalb ![c, n, m] := by
  exact ⟨signedEqTarget n m, (signedEqTargetGraph_eval _).mpr rfl⟩

theorem signedEqTargetGraph_functional {a b n m : V}
    (ha : signedEqTargetGraph.val.Evalb ![a, n, m])
    (hb : signedEqTargetGraph.val.Evalb ![b, n, m]) : a = b := by
  exact ((signedEqTargetGraph_eval _).mp ha).trans ((signedEqTargetGraph_eval _).mp hb).symm

theorem signedLtTargetGraph_total (n m : V) :
    ∃ c, signedLtTargetGraph.val.Evalb ![c, n, m] := by
  exact ⟨signedLtTarget n m, (signedLtTargetGraph_eval _).mpr rfl⟩

theorem signedLtTargetGraph_functional {a b n m : V}
    (ha : signedLtTargetGraph.val.Evalb ![a, n, m])
    (hb : signedLtTargetGraph.val.Evalb ![b, n, m]) : a = b := by
  exact ((signedLtTargetGraph_eval _).mp ha).trans ((signedLtTargetGraph_eval _).mp hb).symm

end Internal

theorem eqTarget_nat (n m : ℕ) : eqTarget n m = eqTargetCode n m := by
  simp only [eqTarget, eqTargetCode, numeralTermCodeValue_nat]
  simpa using (relationCode_eq_cast (V := ℕ) (numeralTermCode n) (numeralTermCode m)).symm

theorem neTarget_nat (n m : ℕ) : neTarget n m = neTargetCode n m := by
  simp only [neTarget, neTargetCode, numeralTermCodeValue_nat]
  simpa using (relationCode_ne_cast (V := ℕ) (numeralTermCode n) (numeralTermCode m)).symm

theorem ltTarget_nat (n m : ℕ) : ltTarget n m = ltTargetCode n m := by
  simp only [ltTarget, ltTargetCode, numeralTermCodeValue_nat]
  simpa using (relationCode_lt_cast (V := ℕ) (numeralTermCode n) (numeralTermCode m)).symm

theorem nltTarget_nat (n m : ℕ) : nltTarget n m = nltTargetCode n m := by
  simp only [nltTarget, nltTargetCode, numeralTermCodeValue_nat]
  simpa using (relationCode_nlt_cast (V := ℕ) (numeralTermCode n) (numeralTermCode m)).symm

theorem signedEqTarget_nat (n m : ℕ) : signedEqTarget n m = signedEqTargetCode n m := by
  by_cases h : n = m <;> simp [signedEqTarget, signedEqTargetCode, h,
    eqTarget_nat, neTarget_nat]

theorem signedLtTarget_nat (n m : ℕ) : signedLtTarget n m = signedLtTargetCode n m := by
  by_cases h : n < m <;> simp [signedLtTarget, signedLtTargetCode, h,
    ltTarget_nat, nltTarget_nat]

theorem eqTargetCode_encode (n m : ℕ) :
    eqTargetCode n m = encode (“↑n = ↑m” : ArithmeticSentence) := by
  have h : (⌜(“↑n = ↑m” : ArithmeticSentence)⌝ : ℕ) = eqTarget n m := by
    change (⌜(“↑n = ↑m” : ArithmeticSentence)⌝ :
      Bootstrapping.Semiformula ℕ ℒₒᵣ 0).val = _
    simp [Sentence.typed_quote_def, eqTarget]
  simpa only [Sentence.quote_eq_encode_nat, eqTarget_nat] using h.symm

theorem neTargetCode_encode (n m : ℕ) :
    neTargetCode n m = encode (“↑n ≠ ↑m” : ArithmeticSentence) := by
  have h : (⌜(“↑n ≠ ↑m” : ArithmeticSentence)⌝ : ℕ) = neTarget n m := by
    change (⌜(“↑n ≠ ↑m” : ArithmeticSentence)⌝ :
      Bootstrapping.Semiformula ℕ ℒₒᵣ 0).val = _
    simp [Sentence.typed_quote_def, neTarget]
  simpa only [Sentence.quote_eq_encode_nat, neTarget_nat] using h.symm

theorem ltTargetCode_encode (n m : ℕ) :
    ltTargetCode n m = encode (“↑n < ↑m” : ArithmeticSentence) := by
  have h : (⌜(“↑n < ↑m” : ArithmeticSentence)⌝ : ℕ) = ltTarget n m := by
    change (⌜(“↑n < ↑m” : ArithmeticSentence)⌝ :
      Bootstrapping.Semiformula ℕ ℒₒᵣ 0).val = _
    simp [Sentence.typed_quote_def, ltTarget]
  simpa only [Sentence.quote_eq_encode_nat, ltTarget_nat] using h.symm

theorem nltTargetCode_encode (n m : ℕ) :
    nltTargetCode n m = encode (“¬(↑n < ↑m)” : ArithmeticSentence) := by
  have h : (⌜(“¬(↑n < ↑m)” : ArithmeticSentence)⌝ : ℕ) = nltTarget n m := by
    change (⌜(“¬(↑n < ↑m)” : ArithmeticSentence)⌝ :
      Bootstrapping.Semiformula ℕ ℒₒᵣ 0).val = _
    simp [Sentence.typed_quote_def, nltTarget]
  simpa only [Sentence.quote_eq_encode_nat, nltTarget_nat] using h.symm

theorem eqTargetGraph_nat_iff (c n m : ℕ) :
    eqTargetGraph.val.Evalb ![c, n, m] ↔ c = eqTargetCode n m := by
  simp [eqTarget_nat]

theorem neTargetGraph_nat_iff (c n m : ℕ) :
    neTargetGraph.val.Evalb ![c, n, m] ↔ c = neTargetCode n m := by
  simp [neTarget_nat]

theorem ltTargetGraph_nat_iff (c n m : ℕ) :
    ltTargetGraph.val.Evalb ![c, n, m] ↔ c = ltTargetCode n m := by
  simp [ltTarget_nat]

theorem nltTargetGraph_nat_iff (c n m : ℕ) :
    nltTargetGraph.val.Evalb ![c, n, m] ↔ c = nltTargetCode n m := by
  simp [nltTarget_nat]

theorem signedEqTargetGraph_nat_iff (c n m : ℕ) :
    signedEqTargetGraph.val.Evalb ![c, n, m] ↔ c = signedEqTargetCode n m := by
  simp [signedEqTarget_nat]

theorem signedLtTargetGraph_nat_iff (c n m : ℕ) :
    signedLtTargetGraph.val.Evalb ![c, n, m] ↔ c = signedLtTargetCode n m := by
  simp [signedLtTarget_nat]

end FailureOfComposition.NativeNumeralComparison
