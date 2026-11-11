/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalExtensionTheta.Soundness
public import FailureOfComposition.NumericalExtensionComposition.Structural.Codes

/-!
# Arithmetic graphs for the B1(8) index and endpoint builders

These definitions interpret the tensor, theta index, output tag, and scheme
code on arbitrary elements of a PA model.  They are the syntactic layer used
for preservation over possibly nonstandard program and proof codes.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalExtensionTheta

open CodedObjectMembership FiniteExtensionChecker NumericalExtensionProofs
open NumericalProductProofs TypedNearProduct

noncomputable section

/-! ## Internal index and endpoint values -/

noncomputable def tensorIndexValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r : V) : V :=
  pairIndexValue
    (compIndexValue q
      (ORingStructure.numeral firstProjectionIndex : V))
    (compIndexValue r
      (ORingStructure.numeral secondProjectionIndex : V))

noncomputable def thetaIndexValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q : V) : V :=
  compIndexValue (ORingStructure.numeral secondProjectionIndex : V)
    (compIndexValue (ORingStructure.numeral extensionCheckerIndex : V)
      (tensorIndexValue q
        (ORingStructure.numeral Kleene.identityIndex : V)))

noncomputable def thetaInstanceCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q t i : V) : V :=
  rightInstanceCodeValue (thetaIndexValue q) (pair t i) i

noncomputable def componentAndCheckerToThetaAxiomCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q t c i : V) : V :=
  impValue (rightInstanceCodeValue q t c)
    (impValue (checkerInstanceCodeValue c i)
      (thetaInstanceCodeValue q t i))

/-! ## Exact Sigma-one graphs -/

noncomputable def tensorIndexGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y q r.
    ∃ a, !compIndexGraph a q !!(firstProjectionIndex) ∧
    ∃ b, !compIndexGraph b r !!(secondProjectionIndex) ∧
      !pairIndexGraph y a b”

noncomputable def thetaIndexGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y q.
    ∃ a, !tensorIndexGraph a q !!(Kleene.identityIndex) ∧
    ∃ b, !compIndexGraph b !!(extensionCheckerIndex) a ∧
      !compIndexGraph y !!(secondProjectionIndex) b”

noncomputable def thetaInstanceCodeGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “y q t i.
    ∃ h, !thetaIndexGraph h q ∧
    ∃ u, !natPairFormula.val u t i ∧
      !rightInstanceCodeGraph y h u i”

noncomputable def componentAndCheckerToThetaAxiomCodeGraph :
    𝚺₁.Semisentence 5 := .mkSigma
  “y q t c i.
    ∃ a, !rightInstanceCodeGraph a q t c ∧
    ∃ b, !checkerInstanceCodeGraph b c i ∧
    ∃ h, !thetaInstanceCodeGraph h q t i ∧
    ∃ u, !impGraph u b h ∧
      !impGraph y a u”

/-- Output-last form used to existentially close all four parameters in the
logical-axiom leaf without expanding the scheme graph. -/
noncomputable def componentAndCheckerToThetaAxiomCodeGraphOutputLast :
    𝚺₁.Semisentence 5 := .mkSigma
  “q t c i y.
    ∃ a, !rightInstanceCodeGraph a q t c ∧
    ∃ b, !checkerInstanceCodeGraph b c i ∧
    ∃ h, !thetaInstanceCodeGraph h q t i ∧
    ∃ u, !impGraph u b h ∧
      !impGraph y a u”

theorem tensorIndexGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y q r : V) :
    Semiformula.Evalb (M := V) ![y, q, r] tensorIndexGraph.val ↔
      y = tensorIndexValue q r := by
  simp [tensorIndexGraph, tensorIndexValue, compIndexGraph_iff,
    pairIndexGraph_iff, Tarski.Structure.numeral_eq_numeral]

theorem thetaIndexGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y q : V) :
    Semiformula.Evalb (M := V) ![y, q] thetaIndexGraph.val ↔
      y = thetaIndexValue q := by
  simp [thetaIndexGraph, thetaIndexValue, tensorIndexGraph_iff,
    compIndexGraph_iff, Tarski.Structure.numeral_eq_numeral]

theorem thetaInstanceCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y q t i : V) :
    Semiformula.Evalb (M := V) ![y, q, t, i]
        thetaInstanceCodeGraph.val ↔
      y = thetaInstanceCodeValue q t i := by
  simp [thetaInstanceCodeGraph, thetaInstanceCodeValue,
    thetaIndexGraph_iff, rightInstanceCodeGraph_iff]

theorem componentAndCheckerToThetaAxiomCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y q t c i : V) :
    Semiformula.Evalb (M := V) ![y, q, t, c, i]
        componentAndCheckerToThetaAxiomCodeGraph.val ↔
      y = componentAndCheckerToThetaAxiomCodeValue q t c i := by
  simp [componentAndCheckerToThetaAxiomCodeGraph,
    componentAndCheckerToThetaAxiomCodeValue,
    rightInstanceCodeGraph_iff, checkerInstanceCodeGraph_iff,
    thetaInstanceCodeGraph_iff, impGraph_iff_impValue]

theorem componentAndCheckerToThetaAxiomCodeGraphOutputLast_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q t c i y : V) :
    Semiformula.Evalb (M := V) ![q, t, c, i, y]
        componentAndCheckerToThetaAxiomCodeGraphOutputLast.val ↔
      y = componentAndCheckerToThetaAxiomCodeValue q t c i := by
  simp [componentAndCheckerToThetaAxiomCodeGraphOutputLast,
    componentAndCheckerToThetaAxiomCodeValue,
    rightInstanceCodeGraph_iff, checkerInstanceCodeGraph_iff,
    thetaInstanceCodeGraph_iff, impGraph_iff_impValue]

/-! ## Totality and functionality -/

theorem tensorIndexGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, q, r]
      tensorIndexGraph.val :=
  ⟨tensorIndexValue q r, (tensorIndexGraph_iff _ _ _).mpr rfl⟩

theorem thetaIndexGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, q]
      thetaIndexGraph.val :=
  ⟨thetaIndexValue q, (thetaIndexGraph_iff _ _).mpr rfl⟩

theorem thetaInstanceCodeGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q t i : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, q, t, i]
      thetaInstanceCodeGraph.val :=
  ⟨thetaInstanceCodeValue q t i,
    (thetaInstanceCodeGraph_iff _ _ _ _).mpr rfl⟩

theorem componentAndCheckerToThetaAxiomCodeGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q t c i : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, q, t, c, i]
      componentAndCheckerToThetaAxiomCodeGraph.val :=
  ⟨componentAndCheckerToThetaAxiomCodeValue q t c i,
    (componentAndCheckerToThetaAxiomCodeGraph_iff _ _ _ _ _).mpr rfl⟩

theorem tensorIndexGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z q r : V}
    (hy : Semiformula.Evalb (M := V) ![y, q, r] tensorIndexGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, q, r] tensorIndexGraph.val) :
    y = z :=
  (tensorIndexGraph_iff y q r).mp hy |>.trans
    ((tensorIndexGraph_iff z q r).mp hz).symm

theorem thetaIndexGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z q : V}
    (hy : Semiformula.Evalb (M := V) ![y, q] thetaIndexGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, q] thetaIndexGraph.val) :
    y = z :=
  (thetaIndexGraph_iff y q).mp hy |>.trans
    ((thetaIndexGraph_iff z q).mp hz).symm

theorem thetaInstanceCodeGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z q t i : V}
    (hy : Semiformula.Evalb (M := V) ![y, q, t, i]
      thetaInstanceCodeGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, q, t, i]
      thetaInstanceCodeGraph.val) : y = z :=
  (thetaInstanceCodeGraph_iff y q t i).mp hy |>.trans
    ((thetaInstanceCodeGraph_iff z q t i).mp hz).symm

theorem componentAndCheckerToThetaAxiomCodeGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z q t c i : V}
    (hy : Semiformula.Evalb (M := V) ![y, q, t, c, i]
      componentAndCheckerToThetaAxiomCodeGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, q, t, c, i]
      componentAndCheckerToThetaAxiomCodeGraph.val) : y = z :=
  (componentAndCheckerToThetaAxiomCodeGraph_iff y q t c i).mp hy |>.trans
    ((componentAndCheckerToThetaAxiomCodeGraph_iff z q t c i).mp hz).symm

/-! ## Standard-natural-number values -/

theorem tensorIndexValue_nat (q r : ℕ) :
    tensorIndexValue q r = TypedNearProduct.tensorIndex q r := by
  simp [tensorIndexValue, pairIndexValue_nat, compIndexValue_nat,
    TypedNearProduct.tensorIndex_eq_canonical, numeral_eq_natCast_app]

theorem thetaIndexValue_nat (q : ℕ) :
    thetaIndexValue q = thetaIndex q := by
  simp [thetaIndexValue, thetaIndex, tensorIndexValue_nat,
    compIndexValue_nat, numeral_eq_natCast_app]

theorem thetaInstanceCodeValue_nat (q t i : ℕ) :
    thetaInstanceCodeValue q t i = thetaInstanceCode q t i := by
  simp [thetaInstanceCodeValue, thetaIndexValue_nat,
    rightInstanceCodeValue_nat, thetaInstanceCode_eq_right,
    nat_pair_eq]

theorem componentAndCheckerToThetaAxiomCodeValue_nat
    (q t c i : ℕ) :
    componentAndCheckerToThetaAxiomCodeValue q t c i =
      componentAndCheckerToThetaAxiomCode q t c i := by
  simp [componentAndCheckerToThetaAxiomCodeValue,
    rightInstanceCodeValue_nat, checkerInstanceCodeValue_nat,
    thetaInstanceCodeValue_nat, impValue_nat,
    componentAndCheckerToThetaAxiomCode_eq_imp]

end

end FailureOfComposition.NumericalExtensionTheta
