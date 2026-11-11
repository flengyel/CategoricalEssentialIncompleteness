/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Metamath

/-!
# Regression test for the Feferman MP proof-sequence layer

Three jobs.

1. **Nonvacuity.** A concrete finite `TheoryPresentation` is built and
   `proofList_mp` is applied to it, so the external preservation theorem is not
   merely true because no `TheoryPresentation` exists. The composite proof list
   is also pinned by `rfl`, so the *shape* of `mpList` is a regression target
   and not only its correctness.

2. **Rejection.** `IsProofList` is shown to fail on the empty list, on a list
   whose last entry is not the claimed conclusion, and on a single-line list
   whose line is neither a logical axiom nor a theory axiom and has no earlier
   lines available as modus-ponens witnesses. Without these, a vacuously true
   `IsProofList` would satisfy every positive test above. `LineJustified` is
   also shown to fail out of range, which is the point of its explicit range
   condition.

3. **Certification.** The structural presentation is extended to a
   `PRTheoryPresentation`, so the `Primrec` layer is exercised on a presentation
   with a nontrivial axiom test rather than left uninhabited.

Signature guards use explicit `@`-ascriptions: a drift in implicit-argument
structure or in argument order fails to elaborate here rather than silently
propagating to `MPSequence.lean`'s downstream consumers.

`#print axioms` is at the end. `scripts/syncpcats.sh` does not apply its
axiom grep to `Tests/`, so the output here is informational; the enforced
check for this root is `check_metamath_axioms.lean`.
-/

@[expose] public section

namespace Metamath.Feferman.Test

open Metamath.Feferman

/-! ### A concrete finite presentation -/

/-- The antecedent used throughout. -/
def aStr : FormulaString := [1]

/-- The consequent used throughout. -/
def bStr : FormulaString := [2]

/-- Every candidate string is a formula. This is the weakest `formula`
predicate satisfying `formula_imp_iff`, and it suffices: the point of the test
is to check the proof-sequence transformations. -/
def allFormulas : StringPredicate where
  test := fun _ => true

/-- No logical axioms. `SyntaxPresentation.logicalAxiom_formula` is then
vacuous, and the only justification available to a line is `ax` or modus ponens
— which is what makes the rejection tests below bite. -/
def noLogicalAxioms : StringPredicate where
  test := fun _ => false

/-- Exactly two axioms: `aStr` and `impString aStr bStr`. -/
def twoAxioms : StringPredicate where
  test := fun φ => decide (φ = aStr ∨ φ = impString aStr bStr)

/-- The syntax presentation. -/
def testSyntax : SyntaxPresentation where
  formula := allFormulas
  logicalAxiom := noLogicalAxioms
  logicalAxiom_formula := fun h => Bool.noConfusion h
  formula_imp_iff := fun _ _ => ⟨fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩

/-- The structural theory presentation. No `Primrec` data appears in it. -/
def testTheory : TheoryPresentation where
  syn := testSyntax
  ax := twoAxioms
  ax_formula := fun _ => rfl

/-! ### Primitive-recursive certification of that presentation -/

/-- The axiom test is primitive recursive.

`PrimrecPred p` is `∃ _ : DecidablePred p, Primrec fun a => decide (p a)`, so
the instance must be destructured out and then reconciled with the one the
field's own elaboration selects. `Decidable` is a subsingleton. -/
theorem primrec_twoAxioms : Primrec twoAxioms.test := by
  have h1 : PrimrecPred fun φ : FormulaString => φ = aStr :=
    Primrec.eq.comp Primrec.id (Primrec.const aStr)
  have h2 : PrimrecPred fun φ : FormulaString => φ = impString aStr bStr :=
    Primrec.eq.comp Primrec.id (Primrec.const (impString aStr bStr))
  obtain ⟨_, h⟩ := h1.or h2
  exact Primrec.of_eq h fun _ => congrArg _ (Subsingleton.elim _ _)

/-- The structural presentation extends to a certified one. -/
def testPRTheory : PRTheoryPresentation where
  toTheory := testTheory
  formula_prim := Primrec.const true
  logicalAxiom_prim := Primrec.const false
  ax_prim := primrec_twoAxioms

/-- The certification layer sits over the structural one without changing it. -/
example : testPRTheory.toTheory = testTheory := rfl

/-! ### Positive tests -/

/-- The one-line proof of the antecedent. -/
def pAnte : ProofSequence := [aStr]

/-- The one-line proof of the implication. -/
def rImp : ProofSequence := [impString aStr bStr]

theorem isProofList_pAnte : IsProofList testTheory pAnte aStr := by
  refine ⟨by simp [pAnte], rfl, ?_⟩
  intro i hi
  have hi0 : i = 0 := by simpa [pAnte] using Nat.lt_one_iff.1 (by simpa [pAnte] using hi)
  subst hi0
  exact ⟨by simp [pAnte], rfl, Or.inr (Or.inl (by decide))⟩

theorem isProofList_rImp : IsProofList testTheory rImp (impString aStr bStr) := by
  refine ⟨by simp [rImp], rfl, ?_⟩
  intro i hi
  have hi0 : i = 0 := by simpa [rImp] using Nat.lt_one_iff.1 (by simpa [rImp] using hi)
  subst hi0
  exact ⟨by simp [rImp], rfl, Or.inr (Or.inl (by decide))⟩

/-- The shape of the composite is pinned, not just its correctness. -/
theorem mpList_shape :
    mpList rImp pAnte = [impString aStr bStr, aStr, bStr] := rfl

/-- Nonvacuity: `proofList_mp` applies to an inhabited presentation and yields a
proof of the consequent. -/
theorem isProofList_mp :
    IsProofList testTheory (mpList rImp pAnte) bStr :=
  proofList_mp isProofList_pAnte isProofList_rImp

/-- The same statement against the pinned literal list. -/
theorem isProofList_literal :
    IsProofList testTheory [impString aStr bStr, aStr, bStr] bStr := by
  rw [← mpList_shape]; exact isProofList_mp

/-! ### Accessor equations -/

example : lhsString (impString aStr bStr) = aStr := lhsString_impString aStr bStr
example : rhsString (impString aStr bStr) = bStr := rhsString_impString aStr bStr

/-- The accessors compute on the concrete instance. -/
example : lhsString (impString aStr bStr) = aStr := rfl
example : rhsString (impString aStr bStr) = bStr := rfl

/-- `impString` is self-delimiting: the tag and the antecedent length are the
first two tokens. -/
example : impString aStr bStr = [0, 1, 1, 2] := rfl

/-- Documented behaviour on strings shorter than two tokens. -/
example : lhsString [] = [] := rfl
example : rhsString [] = [] := rfl
example : lhsString [7] = [] := rfl
example : rhsString [7] = [] := rfl

/-- The first token is ignored: the accessors do not check for `impTag`. -/
example : lhsString [9, 1, 5, 6] = [5] := rfl
example : rhsString [9, 1, 5, 6] = [6] := rfl

/-- `take` and `drop` truncate when the split point exceeds what remains. -/
example : lhsString [0, 7, 5, 6] = [5, 6] := rfl
example : rhsString [0, 7, 5, 6] = [] := rfl

/-! ### Rejection tests -/

/-- The empty list is never a proof. -/
example : ¬ IsProofList testTheory [] bStr := fun h => h.1 rfl

/-- A proof list must end in the formula claimed. -/
example : ¬ IsProofList testTheory pAnte bStr := by
  rintro ⟨-, hlast, -⟩
  exact absurd hlast (by decide)

/-- A line that is neither a logical axiom nor a theory axiom needs earlier
lines to serve as modus-ponens witnesses. Line `0` has none. -/
example : ¬ IsProofList testTheory [bStr] bStr := by
  rintro ⟨-, -, hj⟩
  obtain ⟨-, -, hcase⟩ := hj 0 (by simp)
  rcases hcase with h | h | ⟨j, hj0, -⟩
  · exact Bool.noConfusion h
  · exact absurd h (by decide)
  · exact absurd hj0 (Nat.not_lt_zero j)

/-- `LineJustified` fails out of range. Its range condition is what rules this
out: `[bStr].getD 1 [] = []`, and `[]` is not an axiom of `testTheory`, but a
presentation whose axiom test accepted `[]` would satisfy every other clause at
index `1`. -/
example : ¬ LineJustified testTheory [bStr] 1 := by
  rintro ⟨hlt, -, -⟩
  exact absurd hlt (by simp)

/-- The same range rejection at the first index following the three-line
composite proof list. -/
example : ¬ LineJustified testTheory (mpList rImp pAnte) 3 := by
  rintro ⟨hlt, -, -⟩
  exact absurd hlt (by simp [mpList_shape])

/-! ### Signature guards -/

example : @impString = fun (a b : FormulaString) => impTag :: a.length :: (a ++ b) := rfl
example : @lhsString = fun (s : FormulaString) => (s.drop 2).take (s.getD 1 0) := rfl
example : @rhsString = fun (s : FormulaString) => (s.drop 2).drop (s.getD 1 0) := rfl
example : @mpList = fun (r p : ProofSequence) =>
    r ++ p ++ [rhsString (r.getLastD [])] := rfl

example : @StringPredicate.Holds =
    fun (P : StringPredicate) (φ : FormulaString) => P.test φ = true := rfl

example : @IsProofList = fun (Th : TheoryPresentation) (Ψ : ProofSequence)
    (φ : FormulaString) =>
    Ψ ≠ [] ∧ Ψ.getLastD [] = φ ∧ ∀ i, i < Ψ.length → LineJustified Th Ψ i := rfl

/-- The range condition is the first conjunct of `LineJustified`. -/
example : @LineJustified = fun (Th : TheoryPresentation) (Ψ : ProofSequence) (i : ℕ) =>
    i < Ψ.length ∧
      Th.syn.formula.Holds (Ψ.getD i []) ∧
        (Th.syn.logicalAxiom.Holds (Ψ.getD i []) ∨
          Th.ax.Holds (Ψ.getD i []) ∨
          ∃ j < i, ∃ k < i, Ψ.getD k [] = impString (Ψ.getD j []) (Ψ.getD i [])) := rfl

example : ∀ {Th : TheoryPresentation} {p r : ProofSequence} {a b : FormulaString},
    IsProofList Th p a → IsProofList Th r (impString a b) →
      IsProofList Th (mpList r p) b := @proofList_mp

/-- `proofList_mp` is parameterized by the structural presentation, not by the
certified one. -/
example (p r : ProofSequence) (a b : FormulaString) :
    IsProofList testTheory p a → IsProofList testTheory r (impString a b) →
      IsProofList testTheory (mpList r p) b := proofList_mp

/-- The certification structure exposes the three `Primrec` fields. -/
example : Primrec testPRTheory.toTheory.syn.formula.test := testPRTheory.formula_prim
example : Primrec testPRTheory.toTheory.syn.logicalAxiom.test :=
  testPRTheory.logicalAxiom_prim
example : Primrec testPRTheory.toTheory.ax.test := testPRTheory.ax_prim

example : Primrec₂ impString := primrec_impString
example : Primrec lhsString := primrec_lhsString
example : Primrec rhsString := primrec_rhsString
example : Primrec₂ mpList := primrec_mpList

example : @lhsString_impString = fun (a b : FormulaString) =>
    (lhsString_impString a b : lhsString (impString a b) = a) := rfl
example : @rhsString_impString = fun (a b : FormulaString) =>
    (rhsString_impString a b : rhsString (impString a b) = b) := rfl

/-! ### Axiom report -/

#print axioms proofList_mp
#print axioms isProofList_mp
#print axioms primrec_twoAxioms
#print axioms testPRTheory

end Metamath.Feferman.Test
