/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Metamath

/-!
# Regression test for the explicit natural-number proof codes

Four jobs.

1. **Coding laws.** Both directions of the list bijection, both directions of
   the formula-code bijection, and both directions of the proof-code bijection
   are asserted at theorem level, together with the defining coding equations
   at zero, one, and two elements, the successor decoder equation, and a
   concrete numeral round trip.

2. **Nonvacuity.** A concrete finite `TheoryPresentation` is built, the coded
   inputs are pinned to concrete numerals, and `proof_T_mp` is applied to them.
   The decoded composite and its code are both pinned, so the transformation is
   a regression target and not only its correctness.

3. **Rejection.** `Proof_T` is shown to fail on the code of the empty sequence,
   on a mismatched conclusion, on a one-line sequence whose single line is
   neither a logical axiom nor a theory axiom, and on the arguments of `mp`
   supplied in the wrong order.

4. **Certificates.** All thirteen primitive-recursiveness theorems are
   exercised at their exact signatures.

`#eval` appears only alongside theorem-level assertions, never in place of one.

`#print axioms` is at the end. `scripts/syncpcats.sh` does not apply its axiom
grep to `Tests/`, so the output here is informational; the enforced check for
this root is `check_metamath_axioms.lean`.
-/

@[expose] public section

namespace Metamath.Feferman.CodeTest

open Metamath.Feferman

/-! `bitSpread` and `codeUnpair` are defined by well-founded recursion, so their
equations are sealed and numerals do not reduce by `rfl`. `unseal` makes the
equations available to the kernel, which is what lets the concrete numeral
checks below be discharged by `decide`. The resulting theorems stay within
`{propext, Quot.sound}`. -/

unseal bitSpread codeUnpair

/-! ### Generic coding laws -/

example (xs : List ℕ) : listDecode (listEncode xs) = xs := listDecode_listEncode xs
example (n : ℕ) : listEncode (listDecode n) = n := listEncode_listDecode n

example (φ : FormulaString) : decodeFormula (encodeFormula φ) = φ :=
  decodeFormula_encodeFormula φ
example (a : FormulaCode) : encodeFormula (decodeFormula a) = a :=
  encodeFormula_decodeFormula a

example (Ψ : ProofSequence) : decodeProof (encodeProof Ψ) = Ψ :=
  decodeProof_encodeProof Ψ
example (p : ProofSequenceCode) : encodeProof (decodeProof p) = p :=
  encodeProof_decodeProof p

/-- The empty list codes as `0`. -/
example : listEncode [] = 0 := rfl

/-- The one-element coding equation. -/
example (x : ℕ) : listEncode [x] = codePair x 0 + 1 := rfl

/-- The two-element coding equation. -/
example (x y : ℕ) :
    listEncode [x, y] = codePair x (codePair y 0 + 1) + 1 := rfl

/-- The successor decoder equation. -/
example (n : ℕ) :
    listDecode (n + 1) = (codeUnpair n).1 :: listDecode (codeUnpair n).2 :=
  listDecode_succ n

/-- A concrete numeral round trip. `listDecode 37 = [2, 1, 0]`. -/
example : listEncode (listDecode 37) = 37 := listEncode_listDecode 37

example : listDecode 37 = [2, 1, 0] := by
  have h : listEncode [2, 1, 0] = 37 := by decide
  rw [← h, listDecode_listEncode]

/-! ### The local bit-interleaving pairing -/

example (n : ℕ) : codePair (codeUnpair n).1 (codeUnpair n).2 = n :=
  codePair_codeUnpair n
example (a b : ℕ) : codeUnpair (codePair a b) = (a, b) := codeUnpair_codePair a b
example (n : ℕ) : (codeUnpair n).2 ≤ n := codeUnpair_right_le n
example (n : ℕ) : (codeUnpair n).1 ≤ n := codeUnpair_left_le n
example (n : ℕ) : n ≤ bitSpread n := le_bitSpread n

/-- The interleaving on a concrete pair: `5 = 101` and `3 = 11` interleave to
`27 = 11011`. -/
example : codePair 5 3 = 27 := by decide
example : codeUnpair 47 = (3, 7) := by
  have h : codePair 3 7 = 47 := by decide
  rw [← h, codeUnpair_codePair]

example (n : ℕ) : bitSpread n = n % 2 + 4 * bitSpread (n / 2) := bitSpread_eq n
example (a b : ℕ) :
    codePair a b = a % 2 + 2 * (b % 2) + 4 * codePair (a / 2) (b / 2) :=
  codePair_eq a b
example (n : ℕ) :
    (codeUnpair n).1 = 2 * (codeUnpair (n / 4)).1 + n % 2 := codeUnpair_fst n
example (n : ℕ) :
    (codeUnpair n).2 = 2 * (codeUnpair (n / 4)).2 + (n / 2) % 2 :=
  codeUnpair_snd n

/-- The nesting is not collapsed: the empty sequence and the one-line sequence
whose single line is the empty candidate string have different codes. -/
example : encodeProof [] ≠ encodeProof [[]] :=
  encodeProof_nil_ne_encodeProof_nil_nil

example : encodeProof [] = 0 := rfl
example : encodeProof [[]] = 1 := by decide

/-- A nested proof sequence containing an empty candidate formula string
survives both directions of the coding. -/
example : decodeProof (encodeProof [[], [1], []]) = [[], [1], []] :=
  decodeProof_encodeProof _

example : encodeProof [[], [1], []] ≠ encodeProof [[1]] := by
  intro h
  have := encodeProof_injective h
  exact absurd this (by decide)

/-! ### A concrete finite presentation -/

/-- The antecedent used throughout. -/
def aStr : FormulaString := [1]

/-- The consequent used throughout. -/
def bStr : FormulaString := [2]

/-- Every candidate string is a formula. -/
def allFormulas : StringPredicate where
  test := fun _ => true

/-- No logical axioms, so the only justification available to a line is `ax` or
modus ponens. -/
def noLogicalAxioms : StringPredicate where
  test := fun _ => false

/-- Exactly two axioms: `aStr` and `impString aStr bStr`. `bStr` is neither a
logical axiom nor a theory axiom. -/
def twoAxioms : StringPredicate where
  test := fun φ => decide (φ = aStr ∨ φ = impString aStr bStr)

/-- The syntax presentation. -/
def testSyntax : SyntaxPresentation where
  formula := allFormulas
  logicalAxiom := noLogicalAxioms
  logicalAxiom_formula := fun h => Bool.noConfusion h
  formula_imp_iff := fun _ _ => ⟨fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩

/-- The structural theory presentation. `Proof_T` needs only this. -/
def testTheory : TheoryPresentation where
  syn := testSyntax
  ax := twoAxioms
  ax_formula := fun _ => rfl

/-! ### Primitive-recursive certification of that presentation -/

/-- The axiom test is primitive recursive.

`PrimrecPred p` is `∃ _ : DecidablePred p, Primrec fun a => decide (p a)`, so
the instance must be destructured out and then reconciled with the one the
field's own elaboration selects. `Decidable` is a subsingleton. -/
private theorem primrec_twoAxioms : Primrec twoAxioms.test := by
  have h1 : PrimrecPred fun φ : FormulaString => φ = aStr :=
    Primrec.eq.comp Primrec.id (Primrec.const aStr)
  have h2 : PrimrecPred fun φ : FormulaString => φ = impString aStr bStr :=
    Primrec.eq.comp Primrec.id (Primrec.const (impString aStr bStr))
  obtain ⟨_, h⟩ := h1.or h2
  exact Primrec.of_eq h fun _ => congrArg _ (Subsingleton.elim _ _)

/-- The structural presentation of this file extends to a certified one. -/
private def testPRTheory : PRTheoryPresentation where
  toTheory := testTheory
  formula_prim := Primrec.const true
  logicalAxiom_prim := Primrec.const false
  ax_prim := primrec_twoAxioms

example : testPRTheory.toTheory = testTheory := rfl

/-! ### Concrete codes -/

/-- The code of the one-line proof of the antecedent. -/
def pCode : ProofSequenceCode := encodeProof [aStr]

/-- The code of the one-line proof of the implication. -/
def rCode : ProofSequenceCode := encodeProof [impString aStr bStr]

example : encodeFormula aStr = 2 := by decide
example : encodeFormula bStr = 5 := by decide
example : impString aStr bStr = [0, 1, 1, 2] := rfl
example : encodeFormula (impString aStr bStr) = 8390665 := by decide
example : pCode = 5 := by decide
example : rCode = 70368748372034 := by decide

#eval pCode
#eval rCode
#eval mp rCode pCode

/-! ### The decoded transformation -/

theorem decodeProof_pCode : decodeProof pCode = [aStr] :=
  decodeProof_encodeProof _

theorem decodeProof_rCode : decodeProof rCode = [impString aStr bStr] :=
  decodeProof_encodeProof _

/-- The decoded composite is pinned. -/
theorem decodeProof_mp_rCode_pCode :
    decodeProof (mp rCode pCode) = [impString aStr bStr, aStr, bStr] := by
  rw [decodeProof_mp, decodeProof_pCode, decodeProof_rCode]
  rfl

/-- The code of the composite is pinned. -/
theorem mp_rCode_pCode :
    mp rCode pCode = encodeProof [impString aStr bStr, aStr, bStr] := by
  rw [mp, decodeProof_pCode, decodeProof_rCode]
  rfl

example : mp rCode pCode = 70368748896484 := by
  rw [mp_rCode_pCode]; decide

/-! ### Numerical accessors -/

example : lhs (imp (encodeFormula aStr) (encodeFormula bStr)) = encodeFormula aStr :=
  lhs_imp _ _
example : rhs (imp (encodeFormula aStr) (encodeFormula bStr)) = encodeFormula bStr :=
  rhs_imp _ _

example (a b : FormulaCode) : lhs (imp a b) = a := lhs_imp a b
example (a b : FormulaCode) : rhs (imp a b) = b := rhs_imp a b

example {a b a' b' : FormulaCode} : imp a b = imp a' b' ↔ a = a' ∧ b = b' := imp_inj

/-! ### Positive numerical provability -/

theorem proof_T_pCode : Proof_T testTheory pCode (encodeFormula aStr) := by
  rw [Proof_T, decodeProof_pCode, decodeFormula_encodeFormula]
  refine ⟨by simp, rfl, ?_⟩
  intro i hi
  have hi0 : i = 0 := by simpa using Nat.lt_one_iff.1 (by simpa using hi)
  subst hi0
  exact ⟨by simp, rfl, Or.inr (Or.inl (by decide))⟩

theorem proof_T_rCode :
    Proof_T testTheory rCode (imp (encodeFormula aStr) (encodeFormula bStr)) := by
  rw [Proof_T, decodeProof_rCode, decodeFormula_imp, decodeFormula_encodeFormula,
    decodeFormula_encodeFormula]
  refine ⟨by simp, rfl, ?_⟩
  intro i hi
  have hi0 : i = 0 := by simpa using Nat.lt_one_iff.1 (by simpa using hi)
  subst hi0
  exact ⟨by simp, rfl, Or.inr (Or.inl (by decide))⟩

/-- The conclusion, obtained by the external numerical theorem. -/
theorem proof_T_mp_rCode_pCode :
    Proof_T testTheory (mp rCode pCode) (encodeFormula bStr) :=
  proof_T_mp testTheory proof_T_pCode proof_T_rCode

/-! ### Rejection tests -/

/-- The code `0` of the empty sequence proves nothing. -/
example : ¬ Proof_T testTheory 0 (encodeFormula bStr) := by
  rintro ⟨hne, -, -⟩
  exact hne (by rw [decodeProof, listDecode_zero, List.map_nil])

example : ¬ Proof_T testTheory (encodeProof []) (encodeFormula bStr) := by
  rintro ⟨hne, -, -⟩
  rw [decodeProof_encodeProof] at hne
  exact hne rfl

/-- A mismatched conclusion is rejected. -/
example : ¬ Proof_T testTheory pCode (encodeFormula bStr) := by
  rintro ⟨-, hlast, -⟩
  rw [decodeProof_pCode, decodeFormula_encodeFormula] at hlast
  exact absurd hlast (by decide)

/-- A one-line sequence whose single line is `bStr` is rejected: `bStr` is
neither a logical axiom nor a theory axiom, and line `0` has no earlier lines
to serve as modus-ponens witnesses. -/
example : ¬ Proof_T testTheory (encodeProof [bStr]) (encodeFormula bStr) := by
  rintro ⟨-, -, hj⟩
  rw [decodeProof_encodeProof] at hj
  obtain ⟨-, -, hcase⟩ := hj 0 (by simp)
  rcases hcase with h | h | ⟨j, hj0, -⟩
  · exact Bool.noConfusion h
  · exact absurd h (by decide)
  · exact absurd hj0 (Nat.not_lt_zero j)

/-- The argument order of `mp` is fixed. Supplying the antecedent proof first
yields a sequence whose final line is `rhsString aStr = []`, not `bStr`, so it
does not prove the consequent. -/
theorem decodeProof_mp_pCode_rCode :
    decodeProof (mp pCode rCode) = [aStr, impString aStr bStr, []] := by
  rw [decodeProof_mp, decodeProof_pCode, decodeProof_rCode]
  rfl

example : ¬ Proof_T testTheory (mp pCode rCode) (encodeFormula bStr) := by
  rintro ⟨-, hlast, -⟩
  rw [decodeProof_mp_pCode_rCode, decodeFormula_encodeFormula] at hlast
  exact absurd hlast (by decide)

/-! ### Primitive-recursiveness certificates -/

example : Primrec bitSpread := primrec_bitSpread
example : Primrec₂ codePair := primrec_codePair
example : Primrec codeUnpair := primrec_codeUnpair
example : Primrec listEncode := primrec_listEncode
example : Primrec listDecode := primrec_listDecode
example : Primrec encodeFormula := primrec_encodeFormula
example : Primrec decodeFormula := primrec_decodeFormula
example : Primrec encodeProof := primrec_encodeProof
example : Primrec decodeProof := primrec_decodeProof
example : Primrec₂ imp := primrec_imp
example : Primrec lhs := primrec_lhs
example : Primrec rhs := primrec_rhs
example : Primrec₂ mp := primrec_mp

/-! ### Primitive recursiveness of the numerical proof predicate -/

example (Th : PRTheoryPresentation) :
    PrimrecRel (Proof_T Th.toTheory) :=
  primrecRel_proof_T Th

/-- The certificate applies to the concrete presentation of this file. -/
example : PrimrecRel (Proof_T testPRTheory.toTheory) :=
  primrecRel_proof_T testPRTheory

/-- It is stated over the existing `Proof_T` of this file's `testTheory`, not
over a substitute predicate. -/
example : PrimrecRel (Proof_T testTheory) := primrecRel_proof_T testPRTheory

/-! ### Signature guards -/

example : listEncode [] = 0 := listEncode_nil
example : ∀ (x : ℕ) (xs : List ℕ),
    listEncode (x :: xs) = codePair x (listEncode xs) + 1 := @listEncode_cons
example : listDecode 0 = [] := listDecode_zero
example : ∀ (n : ℕ),
    listDecode (n + 1) = (codeUnpair n).1 :: listDecode (codeUnpair n).2 :=
  @listDecode_succ
example : bitSpread 0 = 0 := bitSpread_zero
example : codeUnpair 0 = (0, 0) := codeUnpair_zero
example : @codePair = fun (a b : ℕ) => bitSpread a + 2 * bitSpread b := rfl
example : ∀ (n : ℕ), codePair (codeUnpair n).1 (codeUnpair n).2 = n :=
  @codePair_codeUnpair
example : ∀ (a b : ℕ), codeUnpair (codePair a b) = (a, b) := @codeUnpair_codePair
example : ∀ (n : ℕ), (codeUnpair n).2 ≤ n := @codeUnpair_right_le

example : @encodeFormula = fun (φ : FormulaString) => listEncode φ := rfl
example : @decodeFormula = fun (a : FormulaCode) => listDecode a := rfl
example : @encodeProof = fun (Ψ : ProofSequence) =>
    listEncode (Ψ.map encodeFormula) := rfl
example : @decodeProof = fun (p : ProofSequenceCode) =>
    (listDecode p).map decodeFormula := rfl

example : @imp = fun (a b : FormulaCode) =>
    encodeFormula (impString (decodeFormula a) (decodeFormula b)) := rfl
example : @lhs = fun (s : FormulaCode) =>
    encodeFormula (lhsString (decodeFormula s)) := rfl
example : @rhs = fun (s : FormulaCode) =>
    encodeFormula (rhsString (decodeFormula s)) := rfl
example : @mp = fun (r p : ProofSequenceCode) =>
    encodeProof (mpList (decodeProof r) (decodeProof p)) := rfl

example : @Proof_T = fun (Th : TheoryPresentation) (p : ProofSequenceCode)
    (a : FormulaCode) => IsProofList Th (decodeProof p) (decodeFormula a) := rfl

example : ∀ (xs : List ℕ), listDecode (listEncode xs) = xs :=
  @listDecode_listEncode
example : ∀ (n : ℕ), listEncode (listDecode n) = n :=
  @listEncode_listDecode
example : ∀ (φ : FormulaString), decodeFormula (encodeFormula φ) = φ :=
  @decodeFormula_encodeFormula
example : ∀ (a : FormulaCode), encodeFormula (decodeFormula a) = a :=
  @encodeFormula_decodeFormula
example : ∀ (Ψ : ProofSequence), decodeProof (encodeProof Ψ) = Ψ :=
  @decodeProof_encodeProof
example : ∀ (p : ProofSequenceCode), encodeProof (decodeProof p) = p :=
  @encodeProof_decodeProof

example : ∀ (a b : FormulaCode),
    decodeFormula (imp a b) = impString (decodeFormula a) (decodeFormula b) :=
  @decodeFormula_imp
example : ∀ (a b : FormulaCode), lhs (imp a b) = a := @lhs_imp
example : ∀ (a b : FormulaCode), rhs (imp a b) = b := @rhs_imp
example : ∀ (r p : ProofSequenceCode),
    decodeProof (mp r p) = mpList (decodeProof r) (decodeProof p) :=
  @decodeProof_mp
example : ∀ {a b a' b' : FormulaCode}, imp a b = imp a' b' ↔ a = a' ∧ b = b' :=
  @imp_inj

example : ∀ (Th : TheoryPresentation) {p r : ProofSequenceCode}
    {a b : FormulaCode}, Proof_T Th p a → Proof_T Th r (imp a b) →
      Proof_T Th (mp r p) b := @proof_T_mp

example : Primrec bitSpread := @primrec_bitSpread
example : Primrec₂ codePair := @primrec_codePair
example : Primrec codeUnpair := @primrec_codeUnpair
example : Primrec listEncode := @primrec_listEncode
example : Primrec listDecode := @primrec_listDecode
example : Primrec encodeFormula := @primrec_encodeFormula
example : Primrec decodeFormula := @primrec_decodeFormula
example : Primrec encodeProof := @primrec_encodeProof
example : Primrec decodeProof := @primrec_decodeProof
example : Primrec₂ imp := @primrec_imp
example : Primrec lhs := @primrec_lhs
example : Primrec rhs := @primrec_rhs
example : Primrec₂ mp := @primrec_mp

example : ∀ (Th : PRTheoryPresentation), PrimrecRel (Proof_T Th.toTheory) :=
  @primrecRel_proof_T

/-! ### Axiom report -/

#print axioms primrecRel_proof_T
#print axioms proof_T_mp
#print axioms proof_T_mp_rCode_pCode
#print axioms Proof_T
#print axioms listDecode
#print axioms listDecode_listEncode
#print axioms listEncode_listDecode
#print axioms codePair_codeUnpair
#print axioms codeUnpair_codePair
#print axioms codeUnpair_right_le
#print axioms primrec_listDecode

end Metamath.Feferman.CodeTest
