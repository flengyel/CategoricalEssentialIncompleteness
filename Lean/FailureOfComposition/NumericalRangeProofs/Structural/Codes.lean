/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.CodedObjectMembership
import FailureOfComposition.NumericalRangeProofs.Soundness
import FailureOfComposition.NumericalProofBridge.Structural.Codes

/-!
# Arithmetic graphs for range-proof formula codes

These graphs internalize the packed computation stage and the two formula-code
builders used by the range proof map.  Their arguments may be arbitrary
elements of a PA model.  Standard-natural-number agreement is proved
separately at the end of the file.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalRangeProofs

open CodedObjectMembership NumericalProofBridge

/-! ## The packed computation stage -/

noncomputable def computationStageValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (e s u i : V) : V :=
  pair e (pair s (pair u i))

noncomputable def computationStageGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “k e s u i.
    ∃ ui, !natPairFormula ui u i ∧
    ∃ sui, !natPairFormula sui s ui ∧
      !natPairFormula k e sui”

theorem computationStageGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (k e s u i : V) :
    Semiformula.Evalb (M := V) ![k, e, s, u, i]
        computationStageGraph.val ↔
      k = computationStageValue e s u i := by
  simp [computationStageGraph, computationStageValue]

theorem computationStageGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (e s u i : V) :
    ∃ k : V, Semiformula.Evalb (M := V) ![k, e, s, u, i]
      computationStageGraph.val :=
  ⟨computationStageValue e s u i,
    (computationStageGraph_iff _ _ _ _ _).mpr rfl⟩

theorem computationStageGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {k l e s u i : V}
    (hk : Semiformula.Evalb (M := V) ![k, e, s, u, i]
      computationStageGraph.val)
    (hl : Semiformula.Evalb (M := V) ![l, e, s, u, i]
      computationStageGraph.val) : k = l :=
  (computationStageGraph_iff k e s u i).mp hk |>.trans
    ((computationStageGraph_iff l e s u i).mp hl).symm

/-! ## Formula-code builders -/

noncomputable def computationAxiomCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (e s u i : V) : V :=
  stageCodeValue (rightSentenceCodeValue e u i)
    (computationStageValue e s u i)

noncomputable def computationAxiomCodeGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “c e s u i.
    ∃ a, !rightSentenceCodeGraph a e u i ∧
    ∃ ui, !natPairFormula ui u i ∧
    ∃ sui, !natPairFormula sui s ui ∧
    ∃ k, !natPairFormula k e sui ∧
      !stageCodeGraph c a k”

theorem computationAxiomCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c e s u i : V) :
    Semiformula.Evalb (M := V) ![c, e, s, u, i]
        computationAxiomCodeGraph.val ↔
      c = computationAxiomCodeValue e s u i := by
  simp [computationAxiomCodeGraph, computationAxiomCodeValue,
    rightSentenceCodeGraph_iff, computationStageValue,
    stageCodeGraph_iff]

theorem computationAxiomCodeGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (e s u i : V) :
    ∃ c : V, Semiformula.Evalb (M := V) ![c, e, s, u, i]
      computationAxiomCodeGraph.val :=
  ⟨computationAxiomCodeValue e s u i,
    (computationAxiomCodeGraph_iff _ _ _ _ _).mpr rfl⟩

theorem computationAxiomCodeGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {c d e s u i : V}
    (hc : Semiformula.Evalb (M := V) ![c, e, s, u, i]
      computationAxiomCodeGraph.val)
    (hd : Semiformula.Evalb (M := V) ![d, e, s, u, i]
      computationAxiomCodeGraph.val) : c = d :=
  (computationAxiomCodeGraph_iff c e s u i).mp hc |>.trans
    ((computationAxiomCodeGraph_iff d e s u i).mp hd).symm

noncomputable def rangeIntroAxiomCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (e r u i : V) : V :=
  impValue (rightInstanceCodeValue e u i)
    (rightInstanceCodeValue r i i)

noncomputable def rangeIntroAxiomCodeGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “c e r u i.
    ∃ a, !rightInstanceCodeGraph a e u i ∧
    ∃ b, !rightInstanceCodeGraph b r i i ∧
      !impGraph c a b”

theorem rangeIntroAxiomCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c e r u i : V) :
    Semiformula.Evalb (M := V) ![c, e, r, u, i]
        rangeIntroAxiomCodeGraph.val ↔
      c = rangeIntroAxiomCodeValue e r u i := by
  simp [rangeIntroAxiomCodeGraph, rangeIntroAxiomCodeValue,
    rightInstanceCodeGraph_iff, impGraph_iff_impValue]

theorem rangeIntroAxiomCodeGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (e r u i : V) :
    ∃ c : V, Semiformula.Evalb (M := V) ![c, e, r, u, i]
      rangeIntroAxiomCodeGraph.val :=
  ⟨rangeIntroAxiomCodeValue e r u i,
    (rangeIntroAxiomCodeGraph_iff _ _ _ _ _).mpr rfl⟩

theorem rangeIntroAxiomCodeGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {c d e r u i : V}
    (hc : Semiformula.Evalb (M := V) ![c, e, r, u, i]
      rangeIntroAxiomCodeGraph.val)
    (hd : Semiformula.Evalb (M := V) ![d, e, r, u, i]
      rangeIntroAxiomCodeGraph.val) : c = d :=
  (rangeIntroAxiomCodeGraph_iff c e r u i).mp hc |>.trans
    ((rangeIntroAxiomCodeGraph_iff d e r u i).mp hd).symm

/-! ## Standard-natural-number agreement -/

theorem computationStageValue_nat (e s u i : ℕ) :
    computationStageValue e s u i = computationStage e s u i := by
  simp [computationStageValue, computationStage, nat_pair_eq]

theorem computationAxiomCodeValue_nat (e s u i : ℕ) :
    computationAxiomCodeValue e s u i = computationAxiomCode e s u i := by
  simp [computationAxiomCodeValue, computationAxiomCode_eq_stage,
    rightSentenceCodeValue_nat, computationStageValue_nat,
    stageCodeValue_nat]

theorem rangeIntroAxiomCodeValue_nat (e r u i : ℕ) :
    rangeIntroAxiomCodeValue e r u i = rangeIntroAxiomCode e r u i := by
  simp [rangeIntroAxiomCodeValue, rangeIntroAxiomCode_eq_imp,
    rightInstanceCodeValue_nat, impValue_nat]

end FailureOfComposition.NumericalRangeProofs
