/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeInternalChecker

/-!
# Output graphs for the internal native checker

The public graphs have output-first coordinates `(bit,derivationCode)`,
`(bit,derivationCode,sequentCode)`, and `(bit,proofCode,formulaCode)`.
Their values read the structurally generated table.  Totality depends only
on the computational axiom-graph hypothesis.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeInternalGraphs

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.NativeInternalSyntax
open FailureOfComposition.NativeInternalChecker

/-- Read entry `d` from the table after `d+1` steps. -/
noncomputable def nativeDerivationCheckValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    (d : V) : V := znth (checkTableValue hA (d + 1)) d

noncomputable def nativeDerivationOfCheckValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    (d s : V) : V :=
  @ite V (nativeDerivationCheckValue hA d = 1 ∧ fstIdx d = s)
    (Classical.propDecidable _) 1 0

noncomputable def nativeProofCheckValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    (d a : V) : V := nativeDerivationOfCheckValue hA d {a}

noncomputable def nativeDerivationCheckGraph (A : 𝚺₁.Semisentence 2) :
    𝚺₁.Semisentence 2 := .mkSigma
  “b d. ∃ t, !(checkTableGraph A).val t (d + 1) ∧ !znthDef b t d”

noncomputable def nativeDerivationOfCheckGraph (A : 𝚺₁.Semisentence 2) :
    𝚺₁.Semisentence 3 := .mkSigma
  “b d s. ∃ db, !(nativeDerivationCheckGraph A).val db d ∧
    ∃ c, !fstIdxDef c d ∧
      ((b = 1 ∧ db = 1 ∧ c = s) ∨ (b = 0 ∧ ¬(db = 1 ∧ c = s)))”

noncomputable def nativeProofCheckGraph (A : 𝚺₁.Semisentence 2) :
    𝚺₁.Semisentence 3 := .mkSigma
  “b d a. ∃ s, !insertDef s a 0 ∧ !(nativeDerivationOfCheckGraph A).val b d s”

theorem nativeDerivationCheckGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    (b d : V) :
    Semiformula.Evalb (M := V) ![b, d] (nativeDerivationCheckGraph A).val ↔
      b = nativeDerivationCheckValue hA d := by
  simp [nativeDerivationCheckGraph, nativeDerivationCheckValue, checkTableGraph_iff hA]

theorem nativeDerivationOfCheckGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    (b d s : V) :
    Semiformula.Evalb (M := V) ![b, d, s] (nativeDerivationOfCheckGraph A).val ↔
      b = nativeDerivationOfCheckValue hA d s := by
  by_cases hc : nativeDerivationCheckValue hA d = 1 ∧ fstIdx d = s
  · simp [nativeDerivationOfCheckGraph, nativeDerivationCheckGraph_iff hA,
      nativeDerivationOfCheckValue, hc]
  · simp [nativeDerivationOfCheckGraph, nativeDerivationCheckGraph_iff hA,
      nativeDerivationOfCheckValue, hc, not_and_or.mp hc]

theorem nativeProofCheckGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    (b d a : V) :
    Semiformula.Evalb (M := V) ![b, d, a] (nativeProofCheckGraph A).val ↔
      b = nativeProofCheckValue hA d a := by
  simp [nativeProofCheckGraph, nativeDerivationOfCheckGraph_iff hA,
    nativeProofCheckValue, singleton_eq_insert, emptyset_def]

theorem nativeDerivationCheckValue_isBit
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    (d : V) : nativeDerivationCheckValue hA d = 0 ∨ nativeDerivationCheckValue hA d = 1 := by
  rw [nativeDerivationCheckValue, checkTableValue_lookup_last]
  exact ruleCheckValue_isBit A _ _

theorem nativeDerivationOfCheckValue_isBit
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    (d s : V) : nativeDerivationOfCheckValue hA d s = 0 ∨
      nativeDerivationOfCheckValue hA d s = 1 := by
  unfold nativeDerivationOfCheckValue
  split_ifs <;> simp

theorem nativeProofCheckValue_isBit
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    (d a : V) : nativeProofCheckValue hA d a = 0 ∨ nativeProofCheckValue hA d a = 1 :=
  nativeDerivationOfCheckValue_isBit hA d {a}

theorem nativeDerivationCheckGraph_existsUnique
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    (d : V) : ∃! b : V,
    Semiformula.Evalb (M := V) ![b, d] (nativeDerivationCheckGraph A).val := by
  simp only [nativeDerivationCheckGraph_iff hA]
  exact existsUnique_eq

theorem nativeDerivationOfCheckGraph_existsUnique
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    (d s : V) : ∃! b : V,
    Semiformula.Evalb (M := V) ![b, d, s] (nativeDerivationOfCheckGraph A).val := by
  simp only [nativeDerivationOfCheckGraph_iff hA]
  exact existsUnique_eq

theorem nativeProofCheckGraph_existsUnique
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    (d a : V) : ∃! b : V,
    Semiformula.Evalb (M := V) ![b, d, a] (nativeProofCheckGraph A).val := by
  simp only [nativeProofCheckGraph_iff hA]
  exact existsUnique_eq

end FailureOfComposition.NativeInternalGraphs
