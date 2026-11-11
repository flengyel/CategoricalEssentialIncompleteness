/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeInternalEquality

/-!
# Canonical and Craig applications of the structural checker

The chosen theory graph gives actual all-model checker interpretations.
For a recursively enumerable theory, its Craig companion also admits a
primitive-recursive numerical axiom test.  The numerical comparison is
guarded at valid formulas; it asserts no uniform executable selection of
such a test from an arbitrary external theory description.

The final adequacy result concerns standard natural numbers.  The internal
transport theorem uses literal equality formula codes and Foundation proofs.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeInternalApplications

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.NativeProofChecker
open FailureOfComposition.NativeInternalSyntax
open FailureOfComposition.NativeInternalGraphs
open FailureOfComposition.NativeInternalCorrectness
open FailureOfComposition.NativeInternalAxiomGraph
open FailureOfComposition.NativeInternalNat
open FailureOfComposition.NativeInternalEquality
open FailureOfComposition.NativeEqualityTransport

/-- The canonical graph recognizes all three actual Foundation predicates
in every PA model, including their rejection cases. -/
theorem canonical_checks_correct
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (S : ArithmeticTheory) [S.Δ₁] (b d s a : V) :
    (Semiformula.Evalb (M := V) ![b, d] (nativeDerivationCheckGraph (canonicalAxiomGraph S)).val ↔
      (b = 1 ∧ Derivation S d) ∨ (b = 0 ∧ ¬Derivation S d)) ∧
    (Semiformula.Evalb (M := V) ![b, d, s]
      (nativeDerivationOfCheckGraph (canonicalAxiomGraph S)).val ↔
      (b = 1 ∧ DerivationOf S d s) ∨ (b = 0 ∧ ¬DerivationOf S d s)) ∧
    (Semiformula.Evalb (M := V) ![b, d, a] (nativeProofCheckGraph (canonicalAxiomGraph S)).val ↔
      (b = 1 ∧ Proof S d a) ∨ (b = 0 ∧ ¬Proof S d a)) :=
  ⟨nativeDerivationCheckGraph_correct (canonicalAxiomGraph_computational S)
      (canonicalAxiomGraph_theory S) b d,
   nativeDerivationOfCheckGraph_correct (canonicalAxiomGraph_computational S)
      (canonicalAxiomGraph_theory S) b d s,
   nativeProofCheckGraph_correct (canonicalAxiomGraph_computational S)
      (canonicalAxiomGraph_theory S) b d a⟩

/-- Existence of an effective numerical test and full-domain comparison with
the structural graphs for the Craig companion. -/
theorem exists_craig_structural_checker (T : ArithmeticTheory) [T.RE] :
    ∃ ax : ℕ → Bool, Primrec ax ∧ AxiomAgreement ax T.craig ∧
      NumericalAxiomAgreement (canonicalAxiomGraph T.craig) ax ∧
      Primrec (nativeEqProofCheckPacked ax) ∧
      (∀ b d : ℕ,
        Semiformula.Evalb (M := ℕ) ![b, d]
          (nativeDerivationCheckGraph (canonicalAxiomGraph T.craig)).val ↔
        b = boolBit (nativeDerivationCheck ax d)) ∧
      (∀ b d s : ℕ,
        Semiformula.Evalb (M := ℕ) ![b, d, s]
          (nativeDerivationOfCheckGraph (canonicalAxiomGraph T.craig)).val ↔
        b = boolBit (nativeDerivationOfCheck ax d s)) ∧
      (∀ b d a : ℕ,
        Semiformula.Evalb (M := ℕ) ![b, d, a]
          (nativeProofCheckGraph (canonicalAxiomGraph T.craig)).val ↔
        b = boolBit (nativeProofCheck ax d a)) ∧
      (∀ p q r : ℕ,
        Semiformula.Evalb (M := ℕ) ![p, q, r]
          (nativeEqCheckFormula (canonicalAxiomGraph T.craig)).val ↔
        nativeEqProofCheck ax p q r = true) := by
  rcases exists_craig_axiomTest T with ⟨ax, hpr, hax⟩
  have hn := canonicalAxiomGraph_numerical hax
  have hc := canonicalAxiomGraph_computational (V := ℕ) T.craig
  exact ⟨ax, hpr, hax, hn, primrec_nativeEqProofCheckPacked hpr,
    nativeDerivationCheckGraph_nat_iff hc hn,
    nativeDerivationOfCheckGraph_nat_iff hc hn,
    nativeProofCheckGraph_nat_iff hc hn, nativeEqCheckFormula_nat_iff hc hn⟩

/-- Adequacy is a standard-model comparison with the existing quotient
relation, not an internal truth interpretation of that relation. -/
theorem craig_eq_acceptance_iff_eqIndex (T : ArithmeticTheory) [T.RE] (q r : ℕ) :
    (∃ p : ℕ, Semiformula.Evalb (M := ℕ) ![p, q, r]
      (nativeEqCheckFormula (canonicalAxiomGraph T.craig)).val) ↔
      FailureOfComposition.UniformIndexQuotient.EqIndex T q r := by
  simp only [nativeEqCheckFormula_iff (canonicalAxiomGraph_computational T.craig)
    (canonicalAxiomGraph_theory T.craig), eqValue_nat]
  exact craig_proof_nativeEqCode_iff_eqIndex T q r

/-- One standard seed works before the recursively enumerable theory and
PA model are chosen. -/
theorem exists_uniform_craig_seed_acceptance :
    ∃ seed : ℕ, Primrec (proofTransportPacked seed) ∧
      ∀ (T : ArithmeticTheory) [T.RE]
        (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔],
      Semiformula.Evalb (M := V) ![1, ORingStructure.numeral seed, (⌜theta⌝ : V)]
        (nativeProofCheckGraph (canonicalAxiomGraph T.craig)).val ∧
      ∀ y e p q r c : V,
        Semiformula.Evalb (M := V)
          ![y, ORingStructure.numeral seed, 0, e, p, q, r, c] transportGraph.val →
        Semiformula.Evalb (M := V) ![e, q, r]
          (nativeEqCheckFormula (canonicalAxiomGraph T.craig)).val →
        Semiformula.Evalb (M := V) ![p, q, c]
          (nativeEqCheckFormula (canonicalAxiomGraph T.craig)).val →
        Semiformula.Evalb (M := V) ![y, r, c]
          (nativeEqCheckFormula (canonicalAxiomGraph T.craig)).val := by
  rcases exists_uniform_seed_acceptance with ⟨seed, hseed⟩
  exact ⟨seed, primrec_proofTransportPacked seed, fun T _ V _ _ => hseed T.craig V⟩

end FailureOfComposition.NativeInternalApplications
