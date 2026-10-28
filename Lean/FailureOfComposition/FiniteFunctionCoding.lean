/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.CodedObjectMembership
import Foundation.FirstOrder.Arithmetic.Exponential.Bit
import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# Binary codes for finite partial functions

Every natural number is a code.  The pair `(n, v)` is present in `c` when the
`Nat.pair n v`-th binary digit of `c` is one.  If several pairs in `c` have the
same input, the least output is selected.  Thus `FiniteEntry c n v` says both
that `(n, v)` is present and that no smaller output for `n` is present.

The arithmetic formula in this file uses Foundation's binary-membership
predicate and arithmetic pairing.  Its standard interpretation therefore uses
`Nat.pair`; it is unrelated to the proof-syntax pairing operation used by the
Feferman proof presentation.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.FiniteFunctionCoding

open CodedObjectMembership

/-! ## External and model-relative finite entries -/

/-- The least-output interpretation of one entry in a binary finite-function
code, stated in an arbitrary arithmetic model. -/
def FiniteEntryModel
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (c n v : M) : Prop :=
  pair n v ∈ c ∧ ∀ w < v, pair n w ∉ c

/-- The finite-value relation on natural codes.  Every `c` is admitted as a
code, and competing output bits are resolved by choosing the least output. -/
def FiniteEntry (c n v : ℕ) : Prop :=
  Nat.pair n v ∈ c ∧ ∀ w < v, Nat.pair n w ∉ c

/-- The arithmetic finite-entry formula, with free variables ordered as code,
input, and output. -/
noncomputable def finiteEntryFormula : 𝚺₀.Semisentence 3 := .mkSigma
  “c n v. :⟪n, v⟫:∈ c ∧ ∀ w < v, ¬:⟪n, w⟫:∈ c”

@[simp] theorem finiteEntryFormula_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (c n v : M) :
    finiteEntryFormula.val.Evalb ![c, n, v] ↔
      FiniteEntryModel c n v := by
  simp [finiteEntryFormula, FiniteEntryModel]

/-- A selected output is unique. -/
theorem finiteEntryModel_functional
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {c n v w : M}
    (hv : FiniteEntryModel c n v) (hw : FiniteEntryModel c n w) :
    v = w := by
  rcases lt_trichotomy v w with hvw | hvw | hwv
  · exact False.elim (hw.2 v hvw hv.1)
  · exact hvw
  · exact False.elim (hv.2 w hwv hw.1)

/-- A present pair has its input below the finite-function code. -/
theorem finiteEntryModel_input_lt
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {c n v : M} (h : FiniteEntryModel c n v) : n < c := by
  exact lt_of_le_of_lt (le_pair_left n v) (lt_of_mem h.1)

/-- A present pair has its selected output below the finite-function code. -/
theorem finiteEntryModel_output_lt
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {c n v : M} (h : FiniteEntryModel c n v) : v < c := by
  exact lt_of_le_of_lt (le_pair_right n v) (lt_of_mem h.1)

theorem finiteEntry_functional {c n v w : ℕ}
    (hv : FiniteEntry c n v) (hw : FiniteEntry c n w) : v = w := by
  rcases lt_trichotomy v w with hvw | hvw | hwv
  · exact False.elim (hw.2 v hvw hv.1)
  · exact hvw
  · exact False.elim (hv.2 w hwv hw.1)

theorem finiteEntry_input_lt {c n v : ℕ}
    (h : FiniteEntry c n v) : n < c := by
  have hpair := lt_of_mem h.1
  have hleft := Nat.left_le_pair n v
  omega

theorem finiteEntry_output_lt {c n v : ℕ}
    (h : FiniteEntry c n v) : v < c := by
  have hpair := lt_of_mem h.1
  have hright := Nat.right_le_pair n v
  omega

/-! ## Standard numeral agreement and primitive recursiveness -/

/-- Finite-entry semantics is absolute on standard numerals in every model of
PA.  The bounded minimality clause is handled explicitly: every model element
below a standard numeral is itself a standard numeral. -/
theorem finiteEntryModel_numeral_iff
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c n v : ℕ) :
    FiniteEntryModel (c : M) (n : M) (v : M) ↔
      FiniteEntry c n v := by
  have hpair (a b : ℕ) :
      pair (a : M) (b : M) = (Nat.pair a b : M) := by
    exact (coe_pair_eq_pair_coe a b).symm
  constructor
  · rintro ⟨hmem, hleast⟩
    constructor
    · exact (mem_absolute (V := M) (Nat.pair n v) c).mpr
        (by simpa only [hpair] using hmem)
    · intro w hw hbit
      have hwM : (w : M) < (v : M) := by simpa using hw
      have hnot := hleast (w : M) hwM
      exact hnot (by
        rw [hpair]
        exact (mem_absolute (V := M) (Nat.pair n w) c).mp hbit)
  · rintro ⟨hmem, hleast⟩
    constructor
    · rw [hpair]
      exact (mem_absolute (V := M) (Nat.pair n v) c).mp hmem
    · intro w hw
      obtain ⟨k, hk, rfl⟩ :=
        (iff_lt_numeral_exists_numeral (M := M)
          (x := w) (n := v)).mp (by
            simpa only [numeral_eq_natCast] using hw)
      intro hbit
      exact hleast k hk
        ((mem_absolute (V := M) (Nat.pair n k) c).mpr (by
          simpa only [numeral_eq_natCast, hpair] using hbit))

@[simp] theorem finiteEntryFormula_numeral_iff
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c n v : ℕ) :
    finiteEntryFormula.val.Evalb ![(c : M), (n : M), (v : M)] ↔
      FiniteEntry c n v := by
  rw [finiteEntryFormula_eval]
  exact finiteEntryModel_numeral_iff c n v

/-- The three-place finite-entry predicate is primitive recursive. -/
theorem primrecPred_finiteEntry :
    PrimrecPred (fun z : (ℕ × ℕ) × ℕ =>
      FiniteEntry z.1.1 z.1.2 z.2) := by
  let emptyAssignment : Empty → ℕ := fun e => nomatch e
  have hformula : PrimrecPred (fun v : List.Vector ℕ 3 =>
      finiteEntryFormula.val.Eval v.get emptyAssignment) :=
    delta0_primrec emptyAssignment finiteEntryFormula.sigma_prop
  have hvector : Primrec (fun z : (ℕ × ℕ) × ℕ =>
      (z.1.1 ::ᵥ z.1.2 ::ᵥ z.2 ::ᵥ List.Vector.nil)) :=
    Primrec.vector_cons.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.vector_cons.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.vector_cons.comp Primrec.snd
          (Primrec.const List.Vector.nil)))
  apply (hformula.comp hvector).of_eq
  intro z
  simp [finiteEntryFormula, FiniteEntry, nat_pair_eq,
    List.Vector.cons_get]

/-! ## Closed conventions used by the checker applications -/

/-- Code zero is the empty finite function. -/
theorem not_finiteEntry_zero (n v : ℕ) :
    ¬FiniteEntry 0 n v := by
  intro h
  exact (not_mem_zero (Nat.pair n v)) h.1

/-- The code with bits for `(0,0)` and `(0,1)` selects only the smaller of
those two competing outputs at input zero. -/
noncomputable def competingZeroOneCode : ℕ :=
  insert (Nat.pair 0 0) (insert (Nat.pair 0 1) 0)

theorem finiteEntry_competing_zero :
    FiniteEntry competingZeroOneCode 0 0 := by
  refine ⟨by simp [competingZeroOneCode], ?_⟩
  intro w hw
  omega

theorem not_finiteEntry_competing_one :
    ¬FiniteEntry competingZeroOneCode 0 1 := by
  intro h
  exact h.2 0 (by omega) (by simp [competingZeroOneCode])

end FailureOfComposition.FiniteFunctionCoding
