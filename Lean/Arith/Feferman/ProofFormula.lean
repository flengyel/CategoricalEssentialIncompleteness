/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Metamath.Feferman.ProofCode
public import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# A Sigma-one arithmetic formula for the Feferman proof predicate

`Metamath.Feferman.Proof_T` is the numerical proof predicate of the Feferman
MP-only proof sequences, and `Metamath.Feferman.primrecRel_proof_T` proves it
primitive recursive. This module transports that certificate through
exact-pinned Foundation's generic arithmetic-representation results and obtains
a named formula whose standard-natural-number semantics agree with `Proof_T`.

`Proof_T` is unchanged. No second proof predicate is defined here, and no
substitute proof calculus is introduced.

## The outer pairing

`Proof_T` is binary and Foundation's `codeOfREPred` is unary, so the two
arguments are combined by `Nat.pair`, with the proof-sequence code first and
the formula code second. `proofTPacked_pair` proves that this combination is
undone exactly. The pairing is an outer arity-reduction device: it is not one
of the project's Feferman codes, it does not identify `Nat.pair` with the
project's `codePair`, and it does not identify the project's list codes with
Foundation's hereditarily finite set codes.

## What is proved, and what is not

* `delta1_proofTPacked` classifies the packed predicate as Delta-one. It is a
  definability classification, not an evaluation theorem for a named Delta-one
  formula.
* `proofTFormula` is a named Sigma-one formula. `proofTFormula_sigma_one`
  proves its hierarchy classification; it is not a named Delta-one formula.
* `proofTFormula_nat_iff` proves standard-natural-number adequacy.
* `proofTFormula_weak_representation` proves numeralwise weak representation.

`proofTFormula_weak_representation` assumes an arithmetic theory `T` with
`𝗥₀ ⪯ T` and `T.SoundOnHierarchy 𝚺 1`, and concludes, for each pair of
natural numbers `p` and `a`, that `Proof_T Th.toTheory p a` holds exactly when
`T` derives the substituted formula `(proofTFormula Th)/[Nat.pair p a]`.

`T` is the theory in which each numeral instance is derivable. It is not
`Th.toTheory`, which specifies the numerical proof predicate instead.

The statement is numeralwise. For a false instance it implies that the
positive substituted formula is not derivable in `T`; it does not imply that
`T` derives the negation of that formula. It does not prove the uniform PA
theorem with free proof and formula variables expressing preservation under the
numerical `mp` operation. That object-language theorem remains absent.

## Axiom envelope

`scripts/syncpcats.sh` checks this root against
`{propext, Classical.choice, Quot.sound}` through `check_arith_axioms.lean`.
-/

@[expose] public section

open Metamath.Feferman FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace Arith.Feferman

/-- The unary form of `Proof_T`, combining its two arguments with `Nat.pair`.
The argument order is fixed: `Nat.pair p a` has the proof-sequence code `p`
first and the formula code `a` second, matching
`Proof_T Th.toTheory p a`. -/
def proofTPacked (Th : PRTheoryPresentation) : ℕ → Prop :=
  fun n => Proof_T Th.toTheory (Nat.unpair n).1 (Nat.unpair n).2

/-- The packing is undone exactly, so the unary form determines `Proof_T` and
changes neither argument. -/
theorem proofTPacked_pair (Th : PRTheoryPresentation) (p a : ℕ) :
    proofTPacked Th (Nat.pair p a) ↔ Proof_T Th.toTheory p a := by
  simp [proofTPacked, Nat.unpair_pair]

/-- `PrimrecRel R` is by definition `PrimrecPred fun q => R q.1 q.2`, but
`PrimrecPred.comp` does not perform that step during unification. The composite
is formed first and checked afterwards. -/
private theorem primrecPred_proofTPacked (Th : PRTheoryPresentation) :
    PrimrecPred (proofTPacked Th) := by
  have h : PrimrecPred fun q : ℕ × ℕ => Proof_T Th.toTheory q.1 q.2 :=
    primrecRel_proof_T Th
  have h2 := PrimrecPred.comp h Primrec.unpair
  exact h2

private theorem computablePred_proofTPacked (Th : PRTheoryPresentation) :
    ComputablePred (proofTPacked Th) := by
  obtain ⟨inst, h⟩ := primrecPred_proofTPacked Th
  exact ⟨inst, h.to_comp⟩

/-- The packed predicate is recursively enumerable, which is what
`codeOfREPred` assumes. -/
theorem rePred_proofTPacked (Th : PRTheoryPresentation) :
    REPred (proofTPacked Th) :=
  (computablePred_proofTPacked Th).to_re

/-- The packed predicate is Delta-one. This is a definability classification of
the predicate; it does not name a Delta-one formula. -/
theorem delta1_proofTPacked (Th : PRTheoryPresentation) :
    𝚫₁-Predicate (proofTPacked Th) :=
  computablePred_iff_delta1.mp (computablePred_proofTPacked Th)

/-- The named arithmetic formula for the packed proof predicate. -/
noncomputable def proofTFormula (Th : PRTheoryPresentation) :
    ArithmeticSemisentence 1 :=
  codeOfREPred (proofTPacked Th)

/-- The named formula is Sigma-one. This is proved, not inferred from the name
of the construction. -/
theorem proofTFormula_sigma_one (Th : PRTheoryPresentation) :
    Hierarchy 𝚺 1 (proofTFormula Th) := by
  simp [proofTFormula, codeOfREPred, codeOfPartrec']

/-- Standard-natural-number adequacy: evaluating `proofTFormula Th` at the
combined code `Nat.pair p a` agrees with `Proof_T Th.toTheory p a`. -/
theorem proofTFormula_nat_iff (Th : PRTheoryPresentation) (p a : ℕ) :
    (Semiformula.Evalb ![Nat.pair p a]) (proofTFormula Th) ↔
      Proof_T Th.toTheory p a := by
  rw [proofTFormula, codeOfREPred_spec (rePred_proofTPacked Th)]
  exact proofTPacked_pair Th p a

/-- Numeralwise weak representation: at each pair of numerals, the packed
form of `Proof_T` holds exactly when `T` derives the substituted formula.

`T` is an arithmetic theory extending `𝗥₀` and sound on `𝚺 1`; it is not
`Th.toTheory`. A false instance implies non-derivability of the positive
substituted formula, not derivability of its negation. -/
theorem proofTFormula_weak_representation
    (Th : PRTheoryPresentation) {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] (p a : ℕ) :
    Proof_T Th.toTheory p a ↔ T ⊢ (proofTFormula Th)/[Nat.pair p a] := by
  rw [← proofTPacked_pair]
  exact rePred_weak_representation (rePred_proofTPacked Th)

end Arith.Feferman
