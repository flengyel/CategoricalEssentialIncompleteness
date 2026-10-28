/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalProductProofs.Soundness
import FailureOfComposition.NumericalProofBridge.Structural

/-!
# Arithmetic graphs for product-definedness codes

The external program-index constructors are polynomial expressions in the
fixed coding of partial-recursive programs.  We repeat those expressions
inside arbitrary models of arithmetic and compose them with the existing
graphs for tagged formulas and implication.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization
open CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition.NumericalProductProofs

open ProofSearch ConcreteEvaluator CodedObjectMembership
open NumericalProofBridge TypedNearProduct TypedProgramCategory
open UniformIndexQuotient

/-! ## Internal program-index constructors -/

noncomputable def pairIndexValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r : V) : V :=
  4 * pair q r + 4

noncomputable def compIndexValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (f g : V) : V :=
  2 * (2 * pair f g + 1) + 4

noncomputable def domainIndexValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q : V) : V :=
  compIndexValue (ORingStructure.numeral firstProjectionIndex : V)
    (pairIndexValue (ORingStructure.numeral Kleene.identityIndex : V) q)

noncomputable def project0PairIndexValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r : V) : V :=
  compIndexValue (ORingStructure.numeral firstProjectionIndex : V)
    (pairIndexValue q r)

noncomputable def project1PairIndexValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r : V) : V :=
  compIndexValue (ORingStructure.numeral secondProjectionIndex : V)
    (pairIndexValue q r)

noncomputable def pairIndexGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y q r. ∃ z, !natPairFormula.val z q r ∧ y = 4 * z + 4”

noncomputable def compIndexGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y f g. ∃ z, !natPairFormula.val z f g ∧
    y = 2 * (2 * z + 1) + 4”

noncomputable def domainIndexGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y q.
    ∃ u, !pairIndexGraph u !!(Kleene.identityIndex) q ∧
      !compIndexGraph y !!(firstProjectionIndex) u”

noncomputable def project0PairIndexGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y q r.
    ∃ u, !pairIndexGraph u q r ∧
      !compIndexGraph y !!(firstProjectionIndex) u”

noncomputable def project1PairIndexGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y q r.
    ∃ u, !pairIndexGraph u q r ∧
      !compIndexGraph y !!(secondProjectionIndex) u”

theorem pairIndexGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y q r : V) :
    Semiformula.Evalb (M := V) ![y, q, r] pairIndexGraph.val ↔
      y = pairIndexValue q r := by
  simp [pairIndexGraph, pairIndexValue]

theorem compIndexGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y f g : V) :
    Semiformula.Evalb (M := V) ![y, f, g] compIndexGraph.val ↔
      y = compIndexValue f g := by
  simp [compIndexGraph, compIndexValue]

theorem domainIndexGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y q : V) :
    Semiformula.Evalb (M := V) ![y, q] domainIndexGraph.val ↔
      y = domainIndexValue q := by
  simp [domainIndexGraph, domainIndexValue, pairIndexGraph_iff,
    compIndexGraph_iff, Tarski.Structure.numeral_eq_numeral]

theorem project0PairIndexGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y q r : V) :
    Semiformula.Evalb (M := V) ![y, q, r]
        project0PairIndexGraph.val ↔
      y = project0PairIndexValue q r := by
  simp [project0PairIndexGraph, project0PairIndexValue,
    pairIndexGraph_iff, compIndexGraph_iff,
    Tarski.Structure.numeral_eq_numeral]

theorem project1PairIndexGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y q r : V) :
    Semiformula.Evalb (M := V) ![y, q, r]
        project1PairIndexGraph.val ↔
      y = project1PairIndexValue q r := by
  simp [project1PairIndexGraph, project1PairIndexValue,
    pairIndexGraph_iff, compIndexGraph_iff,
    Tarski.Structure.numeral_eq_numeral]

theorem pairIndexValue_nat (q r : ℕ) :
    pairIndexValue q r = pairIndex q r := by
  rw [pairIndexValue, pairIndex_eq_canonical,
    canonicalPartrecPairIndex_eq]
  simp only [nat_pair_eq]
  rfl

theorem compIndexValue_nat (f g : ℕ) :
    compIndexValue f g = compIndex f g := by
  rw [compIndexValue, compIndex,
    CategoricalRiceShapiro.PartialRecursive.canonicalPartrecCompIndex_eq]
  simp only [nat_pair_eq]
  rfl

theorem domainIndexValue_nat (q : ℕ) :
    domainIndexValue q = domainIndex q := by
  simp only [domainIndexValue, pairIndexValue_nat, compIndexValue_nat,
    numeral_eq_natCast_app, natCast_nat, domainIndex_eq_canonical]

theorem project0PairIndexValue_nat (q r : ℕ) :
    project0PairIndexValue q r = project0PairIndex q r := by
  simp [project0PairIndexValue, project0PairIndex, pairIndexValue_nat,
    compIndexValue_nat, numeral_eq_natCast_app]

theorem project1PairIndexValue_nat (q r : ℕ) :
    project1PairIndexValue q r = project1PairIndex q r := by
  simp [project1PairIndexValue, project1PairIndex, pairIndexValue_nat,
    compIndexValue_nat, numeral_eq_natCast_app]

/-! ## Definedness tags and schema codes -/

noncomputable def definednessTagValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q n : V) : V :=
  rightInstanceCodeValue (domainIndexValue q) n n

noncomputable def definednessTagGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y q n.
    ∃ d, !domainIndexGraph d q ∧
      !rightInstanceCodeGraph y d n n”

theorem definednessTagGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y q n : V) :
    Semiformula.Evalb (M := V) ![y, q, n] definednessTagGraph.val ↔
      y = definednessTagValue q n := by
  simp [definednessTagGraph, definednessTagValue,
    domainIndexGraph_iff, rightInstanceCodeGraph_iff]

theorem definednessTagValue_nat (q n : ℕ) :
    definednessTagValue q n = definednessTag q n := by
  simp [definednessTagValue, definednessTag, domainIndexValue_nat,
    rightInstanceCodeValue_nat]

noncomputable def project0ToPairAxiomCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r n : V) : V :=
  impValue (definednessTagValue (project0PairIndexValue q r) n)
    (definednessTagValue (pairIndexValue q r) n)

noncomputable def project1ToPairAxiomCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r n : V) : V :=
  impValue (definednessTagValue (project1PairIndexValue q r) n)
    (definednessTagValue (pairIndexValue q r) n)

noncomputable def pairToLeftAxiomCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r n : V) : V :=
  impValue (definednessTagValue (pairIndexValue q r) n)
    (definednessTagValue q n)

noncomputable def pairToRightAxiomCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r n : V) : V :=
  impValue (definednessTagValue (pairIndexValue q r) n)
    (definednessTagValue r n)

noncomputable def componentsToPairAxiomCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r n : V) : V :=
  impValue (definednessTagValue q n)
    (impValue (definednessTagValue r n)
      (definednessTagValue (pairIndexValue q r) n))

noncomputable def project0ToPairAxiomCodeGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “y q r n.
    ∃ j, !project0PairIndexGraph j q r ∧
    ∃ k, !pairIndexGraph k q r ∧
    ∃ a, !definednessTagGraph a j n ∧
    ∃ b, !definednessTagGraph b k n ∧
      !impGraph y a b”

noncomputable def project1ToPairAxiomCodeGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “y q r n.
    ∃ j, !project1PairIndexGraph j q r ∧
    ∃ k, !pairIndexGraph k q r ∧
    ∃ a, !definednessTagGraph a j n ∧
    ∃ b, !definednessTagGraph b k n ∧
      !impGraph y a b”

noncomputable def pairToLeftAxiomCodeGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “y q r n.
    ∃ k, !pairIndexGraph k q r ∧
    ∃ a, !definednessTagGraph a k n ∧
    ∃ b, !definednessTagGraph b q n ∧
      !impGraph y a b”

noncomputable def pairToRightAxiomCodeGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “y q r n.
    ∃ k, !pairIndexGraph k q r ∧
    ∃ a, !definednessTagGraph a k n ∧
    ∃ b, !definednessTagGraph b r n ∧
      !impGraph y a b”

noncomputable def componentsToPairAxiomCodeGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “y q r n.
    ∃ k, !pairIndexGraph k q r ∧
    ∃ a, !definednessTagGraph a q n ∧
    ∃ b, !definednessTagGraph b r n ∧
    ∃ c, !definednessTagGraph c k n ∧
    ∃ u, !impGraph u b c ∧
      !impGraph y a u”

theorem project0ToPairAxiomCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y q r n : V) :
    Semiformula.Evalb (M := V) ![y, q, r, n]
        project0ToPairAxiomCodeGraph.val ↔
      y = project0ToPairAxiomCodeValue q r n := by
  simp [project0ToPairAxiomCodeGraph, project0ToPairAxiomCodeValue,
    project0PairIndexGraph_iff, pairIndexGraph_iff,
    definednessTagGraph_iff, impGraph_iff_impValue]

theorem project1ToPairAxiomCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y q r n : V) :
    Semiformula.Evalb (M := V) ![y, q, r, n]
        project1ToPairAxiomCodeGraph.val ↔
      y = project1ToPairAxiomCodeValue q r n := by
  simp [project1ToPairAxiomCodeGraph, project1ToPairAxiomCodeValue,
    project1PairIndexGraph_iff, pairIndexGraph_iff,
    definednessTagGraph_iff, impGraph_iff_impValue]

theorem pairToLeftAxiomCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y q r n : V) :
    Semiformula.Evalb (M := V) ![y, q, r, n]
        pairToLeftAxiomCodeGraph.val ↔
      y = pairToLeftAxiomCodeValue q r n := by
  simp [pairToLeftAxiomCodeGraph, pairToLeftAxiomCodeValue,
    pairIndexGraph_iff, definednessTagGraph_iff, impGraph_iff_impValue]

theorem pairToRightAxiomCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y q r n : V) :
    Semiformula.Evalb (M := V) ![y, q, r, n]
        pairToRightAxiomCodeGraph.val ↔
      y = pairToRightAxiomCodeValue q r n := by
  simp [pairToRightAxiomCodeGraph, pairToRightAxiomCodeValue,
    pairIndexGraph_iff, definednessTagGraph_iff, impGraph_iff_impValue]

theorem componentsToPairAxiomCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y q r n : V) :
    Semiformula.Evalb (M := V) ![y, q, r, n]
        componentsToPairAxiomCodeGraph.val ↔
      y = componentsToPairAxiomCodeValue q r n := by
  simp [componentsToPairAxiomCodeGraph, componentsToPairAxiomCodeValue,
    pairIndexGraph_iff, definednessTagGraph_iff, impGraph_iff_impValue]

theorem project0ToPairAxiomCodeValue_nat (q r n : ℕ) :
    project0ToPairAxiomCodeValue q r n =
      project0ToPairAxiomCode q r n := by
  simp [project0ToPairAxiomCodeValue, project0PairIndexValue_nat,
    pairIndexValue_nat, definednessTagValue_nat, impValue_nat,
    project0ToPairAxiomCode_eq_imp]

theorem project1ToPairAxiomCodeValue_nat (q r n : ℕ) :
    project1ToPairAxiomCodeValue q r n =
      project1ToPairAxiomCode q r n := by
  simp [project1ToPairAxiomCodeValue, project1PairIndexValue_nat,
    pairIndexValue_nat, definednessTagValue_nat, impValue_nat,
    project1ToPairAxiomCode_eq_imp]

theorem pairToLeftAxiomCodeValue_nat (q r n : ℕ) :
    pairToLeftAxiomCodeValue q r n = pairToLeftAxiomCode q r n := by
  simp [pairToLeftAxiomCodeValue, pairIndexValue_nat,
    definednessTagValue_nat, impValue_nat, pairToLeftAxiomCode_eq_imp]

theorem pairToRightAxiomCodeValue_nat (q r n : ℕ) :
    pairToRightAxiomCodeValue q r n = pairToRightAxiomCode q r n := by
  simp [pairToRightAxiomCodeValue, pairIndexValue_nat,
    definednessTagValue_nat, impValue_nat, pairToRightAxiomCode_eq_imp]

theorem componentsToPairAxiomCodeValue_nat (q r n : ℕ) :
    componentsToPairAxiomCodeValue q r n =
      componentsToPairAxiomCode q r n := by
  simp [componentsToPairAxiomCodeValue, pairIndexValue_nat,
    definednessTagValue_nat, impValue_nat, componentsToPairAxiomCode_eq_imp]

end FailureOfComposition.NumericalProductProofs
