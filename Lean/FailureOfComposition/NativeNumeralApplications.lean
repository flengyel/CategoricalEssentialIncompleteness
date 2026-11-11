/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeNumeralProof
public import FailureOfComposition.NativeNumeralPR

/-!
# Fixed standard seeds and explicit arithmetic proof functions

After a Delta-one theory extending PA-minus is fixed, seven standard seed
codes work in every PA model. They are chosen once, before the model and
numeral inputs. The ensuing numerical functions are explicit and jointly
primitive recursive in the two numeral inputs; their internal outputs have
the exact constructor graphs and are accepted by the canonical native
checker. This supplies the addition and multiplication subcases of later
truth-proof construction, not a selector for proofs of checker acceptance.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

universe u

namespace FailureOfComposition.NativeNumeralArithmetic

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.NativeInternalGraphs
open FailureOfComposition.NativeInternalAxiomGraph

def StandardSeeds (S : ArithmeticTheory) [S.Δ₁] (s : Seeds7 ℕ) : Prop :=
  ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔],
    Proof S (ORingStructure.numeral s.1.1.1 : V) (⌜r0Sentence⌝ : V) ∧
    Proof S (ORingStructure.numeral s.1.1.2 : V) (⌜z1Sentence⌝ : V) ∧
    Proof S (ORingStructure.numeral s.1.2.1 : V) (⌜reflSentence⌝ : V) ∧
    Proof S (ORingStructure.numeral s.1.2.2 : V) (⌜asSentence⌝ : V) ∧
    Proof S (ORingStructure.numeral s.2.1.1 : V) (⌜m0Sentence⌝ : V) ∧
    Proof S (ORingStructure.numeral s.2.1.2 : V) (⌜m1Sentence⌝ : V) ∧
    Proof S (ORingStructure.numeral s.2.2 : V) (⌜msSentence⌝ : V)

private theorem exists_standard_seed (S : ArithmeticTheory) [S.Δ₁]
    (phi : ArithmeticSentence) (hp : S ⊢ phi) :
    ∃ seed : ℕ, ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔],
      Proof S (ORingStructure.numeral seed : V) (⌜phi⌝ : V) := by
  let d : S ⊢! phi := hp.get
  refine ⟨(⌜d⌝ : ℕ), ?_⟩
  intro V _ _
  rw [numeral_eq_natCast_app, coe_quote_proof_eq]
  exact proof_of_quote_proof d

theorem exists_standard_seeds (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔⁻ ⪯ S] :
    ∃ s : Seeds7 ℕ, StandardSeeds.{u} S s := by
  obtain ⟨r0, h0⟩ := exists_standard_seed S _ (WeakerThan.pbl r0_provable)
  obtain ⟨z1, h1⟩ := exists_standard_seed S _ (WeakerThan.pbl z1_provable)
  obtain ⟨refl, hr⟩ := exists_standard_seed S _ (WeakerThan.pbl refl_provable)
  obtain ⟨as, ha⟩ := exists_standard_seed S _ (WeakerThan.pbl as_provable)
  obtain ⟨m0, hm0⟩ := exists_standard_seed S _ (WeakerThan.pbl m0_provable)
  obtain ⟨m1, hm1⟩ := exists_standard_seed S _ (WeakerThan.pbl m1_provable)
  obtain ⟨ms, hms⟩ := exists_standard_seed S _ (WeakerThan.pbl ms_provable)
  refine ⟨(((r0, z1), (refl, as)), ((m0, m1), ms)), ?_⟩
  intro V _ _
  exact ⟨h0 V, h1 V, hr V, ha V, hm0 V, hm1 V, hms V⟩

def addWithSeeds (s : Seeds7 ℕ) (nm : ℕ × ℕ) : ℕ :=
  addCtx s.1.1.1 s.1.1.2 s.1.2.1 s.1.2.2 0 nm.1 nm.2

def mulWithSeeds (s : Seeds7 ℕ) (nm : ℕ × ℕ) : ℕ :=
  mulCtx s.1.1.1 s.1.1.2 s.1.2.1 s.1.2.2 s.2.1.1 s.2.1.2 s.2.2 0 nm.1 nm.2

theorem primrec_addWithSeeds (s : Seeds7 ℕ) : Primrec (addWithSeeds s) :=
  primrec_addCtx (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    (Primrec.const 0) Primrec.fst Primrec.snd

theorem primrec_mulWithSeeds (s : Seeds7 ℕ) : Primrec (mulWithSeeds s) :=
  primrec_mulCtx (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const 0) Primrec.fst Primrec.snd

section Internal

variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

noncomputable def addSeedValue (s : Seeds7 ℕ) (n m : V) : V :=
  addValue (ORingStructure.numeral s.1.1.1) (ORingStructure.numeral s.1.1.2)
    (ORingStructure.numeral s.1.2.1) (ORingStructure.numeral s.1.2.2) 0 n m

noncomputable def mulSeedValue (s : Seeds7 ℕ) (n m : V) : V :=
  mulValue (ORingStructure.numeral s.1.1.1) (ORingStructure.numeral s.1.1.2)
    (ORingStructure.numeral s.1.2.1) (ORingStructure.numeral s.1.2.2)
    (ORingStructure.numeral s.2.1.1) (ORingStructure.numeral s.2.1.2)
    (ORingStructure.numeral s.2.2) 0 n m

theorem standard_arithmetic_endpoint (S : ArithmeticTheory) [S.Δ₁]
    (s : Seeds7 ℕ) (hs : StandardSeeds.{u} S s) (n m : V) :
    addGraph.val.Evalb ![addSeedValue s n m, ORingStructure.numeral s.1.1.1,
      ORingStructure.numeral s.1.1.2, ORingStructure.numeral s.1.2.1,
      ORingStructure.numeral s.1.2.2, 0, n, m] ∧
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, addSeedValue s n m, addEq n m] ∧
    mulGraph.val.Evalb ![mulSeedValue s n m, ORingStructure.numeral s.1.1.1,
      ORingStructure.numeral s.1.1.2, ORingStructure.numeral s.1.2.1,
      ORingStructure.numeral s.1.2.2, ORingStructure.numeral s.2.1.1,
      ORingStructure.numeral s.2.1.2, ORingStructure.numeral s.2.2, 0, n, m] ∧
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, mulSeedValue s n m, mulEq n m] := by
  rcases hs V with ⟨h0, h1, hr, ha, hm0, hm1, hms⟩
  refine ⟨(addGraph_iff _ _ _ _ _ _ _ _).mpr rfl, ?_,
    (mulGraph_iff _ _ _ _ _ _ _ _ _ _ _).mpr rfl, ?_⟩
  · exact (accepted_iff_proof S _ _).mpr (proof_addValue S h0 h1 hr ha)
  · exact (accepted_iff_proof S _ _).mpr (proof_mulValue S h0 h1 hr ha hm0 hm1 hms)

end Internal

theorem addSeedValue_nat (s : Seeds7 ℕ) (n m : ℕ) : addSeedValue s n m = addWithSeeds s (n, m) := by
  simp only [addSeedValue, addWithSeeds, numeral_eq_natCast_app, natCast_nat, addValue_nat]

theorem mulSeedValue_nat (s : Seeds7 ℕ) (n m : ℕ) : mulSeedValue s n m = mulWithSeeds s (n, m) := by
  simp only [mulSeedValue, mulWithSeeds, numeral_eq_natCast_app, natCast_nat, mulValue_nat]

theorem numeral_functions_nat_accepted (S : ArithmeticTheory) [S.Δ₁]
    (s : Seeds7 ℕ) (hs : StandardSeeds.{0} S s) (n m : ℕ) :
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, addWithSeeds s (n, m), addEqCode n m] ∧
    (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
      ![1, mulWithSeeds s (n, m), mulEqCode n m] := by
  have h := standard_arithmetic_endpoint (V := ℕ) S s hs n m
  have ha := h.2.1
  have hm := h.2.2.2
  rw [addSeedValue_nat, addEq_nat] at ha
  rw [mulSeedValue_nat, mulEq_nat] at hm
  exact ⟨ha, hm⟩

theorem exists_standard_arithmetic_functions (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔⁻ ⪯ S] :
    ∃ s : Seeds7 ℕ, StandardSeeds.{u} S s ∧ Primrec (addWithSeeds s) ∧ Primrec (mulWithSeeds s) ∧
      ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔], ∀ n m : V,
        addGraph.val.Evalb ![addSeedValue s n m, ORingStructure.numeral s.1.1.1,
          ORingStructure.numeral s.1.1.2, ORingStructure.numeral s.1.2.1,
          ORingStructure.numeral s.1.2.2, 0, n, m] ∧
        (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
          ![1, addSeedValue s n m, addEq n m] ∧
        mulGraph.val.Evalb ![mulSeedValue s n m, ORingStructure.numeral s.1.1.1,
          ORingStructure.numeral s.1.1.2, ORingStructure.numeral s.1.2.1,
          ORingStructure.numeral s.1.2.2, ORingStructure.numeral s.2.1.1,
          ORingStructure.numeral s.2.1.2, ORingStructure.numeral s.2.2, 0, n, m] ∧
        (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
          ![1, mulSeedValue s n m, mulEq n m] := by
  obtain ⟨s, hs⟩ := exists_standard_seeds S
  refine ⟨s, hs, primrec_addWithSeeds s, primrec_mulWithSeeds s, ?_⟩
  intro V _ _ n m
  exact standard_arithmetic_endpoint S s hs n m

end FailureOfComposition.NativeNumeralArithmetic
