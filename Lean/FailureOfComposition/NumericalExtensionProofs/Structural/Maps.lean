/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalExtensionProofs.Structural.ProofGraph
public import FailureOfComposition.NumericalDomainOrder.Structural.Maps

/-!
# Arithmetic graphs for the two finite-extension proof maps

Each conversion consists of a one-line instance of its recognized scheme and
one numerical modus-ponens step.  The graphs below define the corresponding
internal values on arbitrary, possibly nonstandard, model elements.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalExtensionProofs

noncomputable section

def checkerToExtValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (p c i : V) : V :=
  mpValue (oneLineProofValue (checkerToExtensionAxiomCodeValue c i)) p

def extToCheckerValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (p c i : V) : V :=
  mpValue (oneLineProofValue (extensionToCheckerAxiomCodeValue c i)) p

def checkerToExtGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “y p c i.
    ∃ a, !checkerToExtensionAxiomCodeGraph a c i ∧
    ∃ u, !oneLineProofGraph u a ∧
      !mpGraph y u p”

def extToCheckerGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “y p c i.
    ∃ a, !extensionToCheckerAxiomCodeGraph a c i ∧
    ∃ u, !oneLineProofGraph u a ∧
      !mpGraph y u p”

theorem checkerToExtGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y p c i : V) :
    Semiformula.Evalb (M := V) ![y, p, c, i]
        checkerToExtGraph.val ↔
      y = checkerToExtValue p c i := by
  simp [checkerToExtGraph, checkerToExtValue,
    checkerToExtensionAxiomCodeGraph_iff,
    oneLineProofGraph_iff, mpGraph_iff_mpValue]

theorem extToCheckerGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y p c i : V) :
    Semiformula.Evalb (M := V) ![y, p, c, i]
        extToCheckerGraph.val ↔
      y = extToCheckerValue p c i := by
  simp [extToCheckerGraph, extToCheckerValue,
    extensionToCheckerAxiomCodeGraph_iff,
    oneLineProofGraph_iff, mpGraph_iff_mpValue]

theorem checkerToExtGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (p c i : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, p, c, i]
      checkerToExtGraph.val :=
  ⟨checkerToExtValue p c i,
    (checkerToExtGraph_iff _ _ _ _).mpr rfl⟩

theorem extToCheckerGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (p c i : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, p, c, i]
      extToCheckerGraph.val :=
  ⟨extToCheckerValue p c i,
    (extToCheckerGraph_iff _ _ _ _).mpr rfl⟩

theorem checkerToExtGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z p c i : V}
    (hy : Semiformula.Evalb (M := V) ![y, p, c, i]
      checkerToExtGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, p, c, i]
      checkerToExtGraph.val) :
    y = z :=
  (checkerToExtGraph_iff y p c i).mp hy |>.trans
    ((checkerToExtGraph_iff z p c i).mp hz).symm

theorem extToCheckerGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z p c i : V}
    (hy : Semiformula.Evalb (M := V) ![y, p, c, i]
      extToCheckerGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, p, c, i]
      extToCheckerGraph.val) :
    y = z :=
  (extToCheckerGraph_iff y p c i).mp hy |>.trans
    ((extToCheckerGraph_iff z p c i).mp hz).symm

theorem checkerToExtValue_nat (p c i : ℕ) :
    checkerToExtValue p c i = checkerToExt p c i := by
  simp [checkerToExtValue, checkerToExt,
    checkerToExtensionAxiomCodeValue_nat,
    oneLineProofValue_nat, mpValue_nat]

theorem extToCheckerValue_nat (p c i : ℕ) :
    extToCheckerValue p c i = extToChecker p c i := by
  simp [extToCheckerValue, extToChecker,
    extensionToCheckerAxiomCodeValue_nat,
    oneLineProofValue_nat, mpValue_nat]

/-! ## Internal structural preservation -/

theorem finiteExtensionProofGraph_oneLine
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Th : PRTheoryPresentation) (a : V)
    (ha : Semiformula.Evalb (M := V) ![a]
      finiteExtensionLogicalAxiomLeaf.val) :
    Semiformula.Evalb (M := V) ![oneLineProofValue a, a]
      (proofGraphWithLogicalAxiom Th
        finiteExtensionLogicalAxiomLeaf).val := by
  rw [proofGraphWithLogicalAxiom_iff]
  have hdecode : listDecodeValue (oneLineProofValue a) = a ∷ (0 : V) :=
    listDecodeValue_leftInverse (a ∷ (0 : V))
  rw [hdecode]
  refine ⟨by simp, ?_, ?_⟩
  · simp [lastValue, takeLast_adjoin]
  · intro j hj
    have hj' : j < (1 : V) := by simpa using hj
    have hj0 : j = 0 :=
      le_antisymm (lt_succ_iff_le.mp (by simpa using hj'))
        (Arithmetic.zero_le j)
    subst j
    rw [lineCheckWithLogicalAxiom_iff]
    exact ⟨a, by simp, Or.inl ha⟩

theorem finiteExtensionProofGraph_checkerToExt
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p c i : V)
    (hp : Semiformula.Evalb (M := V)
      ![p, checkerInstanceCodeValue c i]
      (finiteExtensionProofGraph w hw).val) :
    Semiformula.Evalb (M := V)
      ![checkerToExtValue p c i, extensionInstanceCodeValue c i]
      (finiteExtensionProofGraph w hw).val := by
  let Th := finiteExtensionPRTheoryPresentation w hw
  let a := checkerInstanceCodeValue (V := V) c i
  let b := extensionInstanceCodeValue (V := V) c i
  let k := checkerToExtensionAxiomCodeValue (V := V) c i
  let u := oneLineProofValue k
  have hk : Semiformula.Evalb (M := V) ![k, a, b] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hu : Semiformula.Evalb (M := V) ![u, k]
      (proofGraphWithLogicalAxiom Th
        finiteExtensionLogicalAxiomLeaf).val :=
    finiteExtensionProofGraph_oneLine Th k
      (finiteExtensionLogicalAxiomLeaf_checkerToExtension c i)
  have hm : Semiformula.Evalb (M := V)
      ![checkerToExtValue p c i, u, p] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th
    finiteExtensionLogicalAxiomLeaf p a k b u
      (checkerToExtValue p c i) hp hk hu hm

theorem finiteExtensionProofGraph_extToChecker
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p c i : V)
    (hp : Semiformula.Evalb (M := V)
      ![p, extensionInstanceCodeValue c i]
      (finiteExtensionProofGraph w hw).val) :
    Semiformula.Evalb (M := V)
      ![extToCheckerValue p c i, checkerInstanceCodeValue c i]
      (finiteExtensionProofGraph w hw).val := by
  let Th := finiteExtensionPRTheoryPresentation w hw
  let a := extensionInstanceCodeValue (V := V) c i
  let b := checkerInstanceCodeValue (V := V) c i
  let k := extensionToCheckerAxiomCodeValue (V := V) c i
  let u := oneLineProofValue k
  have hk : Semiformula.Evalb (M := V) ![k, a, b] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hu : Semiformula.Evalb (M := V) ![u, k]
      (proofGraphWithLogicalAxiom Th
        finiteExtensionLogicalAxiomLeaf).val :=
    finiteExtensionProofGraph_oneLine Th k
      (finiteExtensionLogicalAxiomLeaf_extensionToChecker c i)
  have hm : Semiformula.Evalb (M := V)
      ![extToCheckerValue p c i, u, p] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th
    finiteExtensionLogicalAxiomLeaf p a k b u
      (extToCheckerValue p c i) hp hk hu hm

end

end FailureOfComposition.NumericalExtensionProofs
