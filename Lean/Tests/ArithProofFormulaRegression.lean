/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import Arith

/-!
# Regression test for the arithmetic formula of the Feferman proof predicate

Three jobs.

1. **Signatures.** Every public declaration of
   `Arith.Feferman.ProofFormula` is exercised at its exact signature, both by
   direct application and by an `@`-ascription guard.

2. **Argument order.** `proofTPacked_pair` is regressed with the
   proof-sequence code first and the formula code second, by direct application
   and by an `@proofTPacked_pair` signature guard.

3. **Semantic distinctions.** Recursive enumerability, the Delta-one predicate
   classification, the named formula's Sigma-one hierarchy classification,
   standard-natural-number adequacy, and numeralwise weak representation are
   regressed separately, because they are different statements.

Numeralwise weak representation is regressed here. It fixes a proof code and a
formula code as numerals: for each such pair, `Proof_T` holds exactly when the
theory `T` derives the substituted formula. The theory `T` is an arithmetic
theory extending `𝗥₀` and sound on `𝚺 1`; it is not `Th.toTheory`.

A false predicate instance therefore implies that `T` does not derive the
positive substituted formula. It does not imply that `T` derives the negation.

No uniform PA theorem over free proof and formula variables is tested, because
none is proved by this development, and no uniform preservation under the
numerical `mp` operation is proved either.

`#print axioms` is informational and appears last. The enforced audit is
`Lean/check_arith_axioms.lean`.
-/

namespace Arith.Feferman.Test

open Metamath.Feferman Arith.Feferman FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

/-! ### Compile-level type guards -/

noncomputable section

example : PRTheoryPresentation → ℕ → Prop := proofTPacked
example : PRTheoryPresentation → ArithmeticSemisentence 1 := @proofTFormula

end

/-! ### Argument order: proof-sequence code first, formula code second -/

example (Th : PRTheoryPresentation) (p a : ℕ) :
    proofTPacked Th (Nat.pair p a) ↔ Proof_T Th.toTheory p a :=
  proofTPacked_pair Th p a

example : ∀ (Th : PRTheoryPresentation) (p a : ℕ),
    proofTPacked Th (Nat.pair p a) ↔ Proof_T Th.toTheory p a :=
  @proofTPacked_pair

/-- The two arguments are not interchangeable in the statement: the left
component of the combined code is the proof-sequence code. -/
example (Th : PRTheoryPresentation) (p a : ℕ) :
    proofTPacked Th (Nat.pair p a) ↔ Proof_T Th.toTheory p a :=
  proofTPacked_pair Th p a

example (Th : PRTheoryPresentation) (n : ℕ) :
    proofTPacked Th n ↔ Proof_T Th.toTheory (Nat.unpair n).1 (Nat.unpair n).2 :=
  Iff.rfl

/-! ### Recursive enumerability -/

example (Th : PRTheoryPresentation) : REPred (proofTPacked Th) :=
  rePred_proofTPacked Th

example : ∀ (Th : PRTheoryPresentation), REPred (proofTPacked Th) :=
  @rePred_proofTPacked

/-! ### Delta-one predicate classification

This classifies the predicate. It does not name a Delta-one formula. -/

example (Th : PRTheoryPresentation) : 𝚫₁-Predicate (proofTPacked Th) :=
  delta1_proofTPacked Th

example : ∀ (Th : PRTheoryPresentation), 𝚫₁-Predicate (proofTPacked Th) :=
  @delta1_proofTPacked

/-! ### The named formula and its Sigma-one hierarchy classification -/

noncomputable example (Th : PRTheoryPresentation) : ArithmeticSemisentence 1 :=
  proofTFormula Th

example (Th : PRTheoryPresentation) : Hierarchy 𝚺 1 (proofTFormula Th) :=
  proofTFormula_sigma_one Th

example : ∀ (Th : PRTheoryPresentation), Hierarchy 𝚺 1 (proofTFormula Th) :=
  @proofTFormula_sigma_one

/-! ### Standard-natural-number adequacy -/

example (Th : PRTheoryPresentation) (p a : ℕ) :
    (Semiformula.Evalb ![Nat.pair p a]) (proofTFormula Th) ↔
      Proof_T Th.toTheory p a :=
  proofTFormula_nat_iff Th p a

example : ∀ (Th : PRTheoryPresentation) (p a : ℕ),
    (Semiformula.Evalb ![Nat.pair p a]) (proofTFormula Th) ↔
      Proof_T Th.toTheory p a :=
  @proofTFormula_nat_iff

/-- Adequacy is stated over the existing `Proof_T`, so it composes with the
existing external numerical modus-ponens theorem. -/
example (Th : PRTheoryPresentation) {p r a b : ℕ}
    (hp : (Semiformula.Evalb ![Nat.pair p a]) (proofTFormula Th))
    (hr : (Semiformula.Evalb ![Nat.pair r (imp a b)]) (proofTFormula Th)) :
    (Semiformula.Evalb ![Nat.pair (mp r p) b]) (proofTFormula Th) := by
  rw [proofTFormula_nat_iff] at hp hr ⊢
  exact proof_T_mp Th.toTheory hp hr

/-! ### Numeralwise weak representation

Distinct from standard-natural-number adequacy above: adequacy evaluates the
formula in the standard model, whereas this states derivability in `T`. -/

example (Th : PRTheoryPresentation) {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] (p a : ℕ) :
    Proof_T Th.toTheory p a ↔ T ⊢ (proofTFormula Th)/[Nat.pair p a] :=
  proofTFormula_weak_representation Th p a

/-- Together with the direct-application example above, this `@`-ascription
fixes binder order, both instance parameters, and the order `p a`; the direct
application also detects that `T` is implicit. -/
example : ∀ (Th : PRTheoryPresentation) (T : ArithmeticTheory)
    (_ : 𝗥₀ ⪯ T) (_ : T.SoundOnHierarchy 𝚺 1) (p a : ℕ),
    Proof_T Th.toTheory p a ↔ T ⊢ (proofTFormula Th)/[Nat.pair p a] :=
  @proofTFormula_weak_representation

/-! ### Signature guard for the packed definition -/

example : @proofTPacked = fun (Th : PRTheoryPresentation) (n : ℕ) =>
    Proof_T Th.toTheory (Nat.unpair n).1 (Nat.unpair n).2 := rfl

/-! ### Axiom report -/

#print axioms proofTPacked
#print axioms proofTPacked_pair
#print axioms rePred_proofTPacked
#print axioms delta1_proofTPacked
#print axioms proofTFormula
#print axioms proofTFormula_sigma_one
#print axioms proofTFormula_nat_iff
#print axioms proofTFormula_weak_representation

end Arith.Feferman.Test
