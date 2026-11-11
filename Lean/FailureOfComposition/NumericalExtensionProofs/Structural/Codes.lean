/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalExtensionProofs.Soundness
public import FailureOfComposition.NumericalDomainOrder.Structural.Codes

/-!
# Arithmetic graphs for finite-extension endpoint and scheme codes

The graphs in this file interpret the data pair internally using Foundation's
arithmetic pairing.  They then reuse the accepted right-instance and
implication graphs, so their standard values are the exact external graph-tag
codes from `NumericalExtensionProofs.Core`.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalExtensionProofs

open CodedObjectMembership FiniteExtensionChecker NumericalProofBridge

noncomputable section

/-! ## Endpoint-code graphs -/

def checkerInstanceCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (c i : V) : V :=
  rightInstanceCodeValue
    (ORingStructure.numeral extensionCheckerIndex : V)
    (pair c i) (pair c i)

def extensionInstanceCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (c i : V) : V :=
  rightInstanceCodeValue
    (ORingStructure.numeral zeroTestIndex : V) (pair c i) 0

def checkerInstanceCodeGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y c i. ∃ u, !natPairFormula.val u c i ∧
    !rightInstanceCodeGraph y !!(extensionCheckerIndex) u u”

def extensionInstanceCodeGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y c i. ∃ u, !natPairFormula.val u c i ∧
    !rightInstanceCodeGraph y !!(zeroTestIndex) u 0”

theorem checkerInstanceCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y c i : V) :
    Semiformula.Evalb (M := V) ![y, c, i]
        checkerInstanceCodeGraph.val ↔
      y = checkerInstanceCodeValue c i := by
  simp [checkerInstanceCodeGraph, checkerInstanceCodeValue,
    rightInstanceCodeGraph_iff,
    Tarski.Structure.numeral_eq_numeral]

theorem extensionInstanceCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y c i : V) :
    Semiformula.Evalb (M := V) ![y, c, i]
        extensionInstanceCodeGraph.val ↔
      y = extensionInstanceCodeValue c i := by
  simp [extensionInstanceCodeGraph, extensionInstanceCodeValue,
    rightInstanceCodeGraph_iff,
    Tarski.Structure.numeral_eq_numeral]

theorem checkerInstanceCodeGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c i : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, c, i]
      checkerInstanceCodeGraph.val :=
  ⟨checkerInstanceCodeValue c i,
    (checkerInstanceCodeGraph_iff _ _ _).mpr rfl⟩

theorem extensionInstanceCodeGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c i : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, c, i]
      extensionInstanceCodeGraph.val :=
  ⟨extensionInstanceCodeValue c i,
    (extensionInstanceCodeGraph_iff _ _ _).mpr rfl⟩

theorem checkerInstanceCodeGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z c i : V}
    (hy : Semiformula.Evalb (M := V) ![y, c, i]
      checkerInstanceCodeGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, c, i]
      checkerInstanceCodeGraph.val) :
    y = z :=
  (checkerInstanceCodeGraph_iff y c i).mp hy |>.trans
    ((checkerInstanceCodeGraph_iff z c i).mp hz).symm

theorem extensionInstanceCodeGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z c i : V}
    (hy : Semiformula.Evalb (M := V) ![y, c, i]
      extensionInstanceCodeGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, c, i]
      extensionInstanceCodeGraph.val) :
    y = z :=
  (extensionInstanceCodeGraph_iff y c i).mp hy |>.trans
    ((extensionInstanceCodeGraph_iff z c i).mp hz).symm

theorem checkerInstanceCodeValue_nat (c i : ℕ) :
    checkerInstanceCodeValue c i = checkerInstanceCode c i := by
  simp [checkerInstanceCodeValue, rightInstanceCodeValue_nat,
    checkerInstanceCode_eq_right, numeral_eq_natCast_app, nat_pair_eq]

theorem extensionInstanceCodeValue_nat (c i : ℕ) :
    extensionInstanceCodeValue c i = extensionInstanceCode c i := by
  simp [extensionInstanceCodeValue, rightInstanceCodeValue_nat,
    extensionInstanceCode_eq_right, numeral_eq_natCast_app, nat_pair_eq]

/-! ## Scheme-code graphs -/

def checkerToExtensionAxiomCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (c i : V) : V :=
  impValue (checkerInstanceCodeValue c i)
    (extensionInstanceCodeValue c i)

def extensionToCheckerAxiomCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (c i : V) : V :=
  impValue (extensionInstanceCodeValue c i)
    (checkerInstanceCodeValue c i)

def checkerToExtensionAxiomCodeGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y c i.
    ∃ a, !checkerInstanceCodeGraph a c i ∧
    ∃ b, !extensionInstanceCodeGraph b c i ∧
      !impGraph y a b”

def extensionToCheckerAxiomCodeGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y c i.
    ∃ a, !extensionInstanceCodeGraph a c i ∧
    ∃ b, !checkerInstanceCodeGraph b c i ∧
      !impGraph y a b”

theorem checkerToExtensionAxiomCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y c i : V) :
    Semiformula.Evalb (M := V) ![y, c, i]
        checkerToExtensionAxiomCodeGraph.val ↔
      y = checkerToExtensionAxiomCodeValue c i := by
  simp [checkerToExtensionAxiomCodeGraph,
    checkerToExtensionAxiomCodeValue, checkerInstanceCodeGraph_iff,
    extensionInstanceCodeGraph_iff, impGraph_iff_impValue]

theorem extensionToCheckerAxiomCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y c i : V) :
    Semiformula.Evalb (M := V) ![y, c, i]
        extensionToCheckerAxiomCodeGraph.val ↔
      y = extensionToCheckerAxiomCodeValue c i := by
  simp [extensionToCheckerAxiomCodeGraph,
    extensionToCheckerAxiomCodeValue, checkerInstanceCodeGraph_iff,
    extensionInstanceCodeGraph_iff, impGraph_iff_impValue]

theorem checkerToExtensionAxiomCodeGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c i : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, c, i]
      checkerToExtensionAxiomCodeGraph.val :=
  ⟨checkerToExtensionAxiomCodeValue c i,
    (checkerToExtensionAxiomCodeGraph_iff _ _ _).mpr rfl⟩

theorem extensionToCheckerAxiomCodeGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c i : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, c, i]
      extensionToCheckerAxiomCodeGraph.val :=
  ⟨extensionToCheckerAxiomCodeValue c i,
    (extensionToCheckerAxiomCodeGraph_iff _ _ _).mpr rfl⟩

theorem checkerToExtensionAxiomCodeGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z c i : V}
    (hy : Semiformula.Evalb (M := V) ![y, c, i]
      checkerToExtensionAxiomCodeGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, c, i]
      checkerToExtensionAxiomCodeGraph.val) :
    y = z :=
  (checkerToExtensionAxiomCodeGraph_iff y c i).mp hy |>.trans
    ((checkerToExtensionAxiomCodeGraph_iff z c i).mp hz).symm

theorem extensionToCheckerAxiomCodeGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z c i : V}
    (hy : Semiformula.Evalb (M := V) ![y, c, i]
      extensionToCheckerAxiomCodeGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, c, i]
      extensionToCheckerAxiomCodeGraph.val) :
    y = z :=
  (extensionToCheckerAxiomCodeGraph_iff y c i).mp hy |>.trans
    ((extensionToCheckerAxiomCodeGraph_iff z c i).mp hz).symm

theorem checkerToExtensionAxiomCodeValue_nat (c i : ℕ) :
    checkerToExtensionAxiomCodeValue c i =
      checkerToExtensionAxiomCode c i := by
  simp [checkerToExtensionAxiomCodeValue,
    checkerInstanceCodeValue_nat, extensionInstanceCodeValue_nat,
    impValue_nat, checkerToExtensionAxiomCode_eq_imp]

theorem extensionToCheckerAxiomCodeValue_nat (c i : ℕ) :
    extensionToCheckerAxiomCodeValue c i =
      extensionToCheckerAxiomCode c i := by
  simp [extensionToCheckerAxiomCodeValue,
    checkerInstanceCodeValue_nat, extensionInstanceCodeValue_nat,
    impValue_nat, extensionToCheckerAxiomCode_eq_imp]

end

end FailureOfComposition.NumericalExtensionProofs
