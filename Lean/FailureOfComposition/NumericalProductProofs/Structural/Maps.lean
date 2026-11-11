/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalProductProofs.Structural.ProofGraph

/-!
# Arithmetic graphs of the product proof maps

Each external primitive-recursive transformation has a model-internal value
and a `𝚺₁` graph.  The graph computes the external function over `ℕ`; over an
arbitrary model of PA, the same value preserves the product proof graph.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization
open CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition.NumericalProductProofs

open ProofSearch ConcreteEvaluator NumericalProofBridge

/-! ## Values and graphs -/

noncomputable def project0ToPairValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (p q r n : V) : V :=
  mpValue (oneLineProofValue (project0ToPairAxiomCodeValue q r n)) p

noncomputable def project1ToPairValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (p q r n : V) : V :=
  mpValue (oneLineProofValue (project1ToPairAxiomCodeValue q r n)) p

noncomputable def pairToLeftValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (p q r n : V) : V :=
  mpValue (oneLineProofValue (pairToLeftAxiomCodeValue q r n)) p

noncomputable def pairToRightValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (p q r n : V) : V :=
  mpValue (oneLineProofValue (pairToRightAxiomCodeValue q r n)) p

noncomputable def componentsToPairValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (p h q r n : V) : V :=
  mpValue
    (mpValue (oneLineProofValue (componentsToPairAxiomCodeValue q r n)) p)
    h

noncomputable def project0ToPairGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “y p q r n.
    ∃ c, !project0ToPairAxiomCodeGraph c q r n ∧
    ∃ u, !oneLineProofGraph u c ∧
      !mpGraph y u p”

noncomputable def project1ToPairGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “y p q r n.
    ∃ c, !project1ToPairAxiomCodeGraph c q r n ∧
    ∃ u, !oneLineProofGraph u c ∧
      !mpGraph y u p”

noncomputable def pairToLeftGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “y p q r n.
    ∃ c, !pairToLeftAxiomCodeGraph c q r n ∧
    ∃ u, !oneLineProofGraph u c ∧
      !mpGraph y u p”

noncomputable def pairToRightGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “y p q r n.
    ∃ c, !pairToRightAxiomCodeGraph c q r n ∧
    ∃ u, !oneLineProofGraph u c ∧
      !mpGraph y u p”

noncomputable def componentsToPairGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “y p h q r n.
    ∃ c, !componentsToPairAxiomCodeGraph c q r n ∧
    ∃ u, !oneLineProofGraph u c ∧
    ∃ v, !mpGraph v u p ∧
      !mpGraph y v h”

theorem project0ToPairGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y p q r n : V) :
    Semiformula.Evalb (M := V) ![y, p, q, r, n]
        project0ToPairGraph.val ↔
      y = project0ToPairValue p q r n := by
  simp [project0ToPairGraph, project0ToPairValue,
    project0ToPairAxiomCodeGraph_iff, oneLineProofGraph_iff,
    mpGraph_iff_mpValue]

theorem project1ToPairGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y p q r n : V) :
    Semiformula.Evalb (M := V) ![y, p, q, r, n]
        project1ToPairGraph.val ↔
      y = project1ToPairValue p q r n := by
  simp [project1ToPairGraph, project1ToPairValue,
    project1ToPairAxiomCodeGraph_iff, oneLineProofGraph_iff,
    mpGraph_iff_mpValue]

theorem pairToLeftGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y p q r n : V) :
    Semiformula.Evalb (M := V) ![y, p, q, r, n]
        pairToLeftGraph.val ↔
      y = pairToLeftValue p q r n := by
  simp [pairToLeftGraph, pairToLeftValue, pairToLeftAxiomCodeGraph_iff,
    oneLineProofGraph_iff, mpGraph_iff_mpValue]

theorem pairToRightGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y p q r n : V) :
    Semiformula.Evalb (M := V) ![y, p, q, r, n]
        pairToRightGraph.val ↔
      y = pairToRightValue p q r n := by
  simp [pairToRightGraph, pairToRightValue, pairToRightAxiomCodeGraph_iff,
    oneLineProofGraph_iff, mpGraph_iff_mpValue]

theorem componentsToPairGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y p h q r n : V) :
    Semiformula.Evalb (M := V) ![y, p, h, q, r, n]
        componentsToPairGraph.val ↔
      y = componentsToPairValue p h q r n := by
  simp [componentsToPairGraph, componentsToPairValue,
    componentsToPairAxiomCodeGraph_iff, oneLineProofGraph_iff,
    mpGraph_iff_mpValue]

/-! ## Totality and functionality -/

theorem project0ToPairGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (p q r n : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, p, q, r, n]
      project0ToPairGraph.val :=
  ⟨project0ToPairValue p q r n,
    (project0ToPairGraph_iff _ _ _ _ _).mpr rfl⟩

theorem project0ToPairGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z p q r n : V}
    (hy : Semiformula.Evalb (M := V) ![y, p, q, r, n]
      project0ToPairGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, p, q, r, n]
      project0ToPairGraph.val) :
    y = z :=
  (project0ToPairGraph_iff y p q r n).mp hy |>.trans
    ((project0ToPairGraph_iff z p q r n).mp hz).symm

theorem project1ToPairGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (p q r n : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, p, q, r, n]
      project1ToPairGraph.val :=
  ⟨project1ToPairValue p q r n,
    (project1ToPairGraph_iff _ _ _ _ _).mpr rfl⟩

theorem project1ToPairGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z p q r n : V}
    (hy : Semiformula.Evalb (M := V) ![y, p, q, r, n]
      project1ToPairGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, p, q, r, n]
      project1ToPairGraph.val) :
    y = z :=
  (project1ToPairGraph_iff y p q r n).mp hy |>.trans
    ((project1ToPairGraph_iff z p q r n).mp hz).symm

theorem pairToLeftGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (p q r n : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, p, q, r, n]
      pairToLeftGraph.val :=
  ⟨pairToLeftValue p q r n,
    (pairToLeftGraph_iff _ _ _ _ _).mpr rfl⟩

theorem pairToLeftGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z p q r n : V}
    (hy : Semiformula.Evalb (M := V) ![y, p, q, r, n]
      pairToLeftGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, p, q, r, n]
      pairToLeftGraph.val) :
    y = z :=
  (pairToLeftGraph_iff y p q r n).mp hy |>.trans
    ((pairToLeftGraph_iff z p q r n).mp hz).symm

theorem pairToRightGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (p q r n : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, p, q, r, n]
      pairToRightGraph.val :=
  ⟨pairToRightValue p q r n,
    (pairToRightGraph_iff _ _ _ _ _).mpr rfl⟩

theorem pairToRightGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z p q r n : V}
    (hy : Semiformula.Evalb (M := V) ![y, p, q, r, n]
      pairToRightGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, p, q, r, n]
      pairToRightGraph.val) :
    y = z :=
  (pairToRightGraph_iff y p q r n).mp hy |>.trans
    ((pairToRightGraph_iff z p q r n).mp hz).symm

theorem componentsToPairGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (p h q r n : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, p, h, q, r, n]
      componentsToPairGraph.val :=
  ⟨componentsToPairValue p h q r n,
    (componentsToPairGraph_iff _ _ _ _ _ _).mpr rfl⟩

theorem componentsToPairGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z p h q r n : V}
    (hy : Semiformula.Evalb (M := V) ![y, p, h, q, r, n]
      componentsToPairGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, p, h, q, r, n]
      componentsToPairGraph.val) :
    y = z :=
  (componentsToPairGraph_iff y p h q r n).mp hy |>.trans
    ((componentsToPairGraph_iff z p h q r n).mp hz).symm

theorem project0ToPairValue_nat (p q r n : ℕ) :
    project0ToPairValue p q r n = project0ToPair p q r n := by
  simp [project0ToPairValue, project0ToPair, oneLineProofValue_nat,
    project0ToPairAxiomCodeValue_nat, mpValue_nat]

theorem project1ToPairValue_nat (p q r n : ℕ) :
    project1ToPairValue p q r n = project1ToPair p q r n := by
  simp [project1ToPairValue, project1ToPair, oneLineProofValue_nat,
    project1ToPairAxiomCodeValue_nat, mpValue_nat]

theorem pairToLeftValue_nat (p q r n : ℕ) :
    pairToLeftValue p q r n = pairToLeft p q r n := by
  simp [pairToLeftValue, pairToLeft, oneLineProofValue_nat,
    pairToLeftAxiomCodeValue_nat, mpValue_nat]

theorem pairToRightValue_nat (p q r n : ℕ) :
    pairToRightValue p q r n = pairToRight p q r n := by
  simp [pairToRightValue, pairToRight, oneLineProofValue_nat,
    pairToRightAxiomCodeValue_nat, mpValue_nat]

theorem componentsToPairValue_nat (p h q r n : ℕ) :
    componentsToPairValue p h q r n = componentsToPair p h q r n := by
  simp [componentsToPairValue, componentsToPair, oneLineProofValue_nat,
    componentsToPairAxiomCodeValue_nat, mpValue_nat]

/-! ## Internal preservation of the proof graph -/

theorem productProofGraph_oneLine
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Th : PRTheoryPresentation) (a : V)
    (ha : Semiformula.Evalb (M := V) ![a]
      productLogicalAxiomLeaf.val) :
    Semiformula.Evalb (M := V) ![oneLineProofValue a, a]
      (proofGraphWithLogicalAxiom Th productLogicalAxiomLeaf).val := by
  rw [proofGraphWithLogicalAxiom_iff]
  have hdecode : listDecodeValue (oneLineProofValue a) = a ∷ (0 : V) :=
    listDecodeValue_leftInverse (a ∷ (0 : V))
  rw [hdecode]
  refine ⟨by simp, ?_, ?_⟩
  · simp [lastValue, takeLast_adjoin]
  · intro i hi
    have hi' : i < (1 : V) := by simpa using hi
    have hi0 : i = 0 :=
      le_antisymm (lt_succ_iff_le.mp (by simpa using hi'))
        (Arithmetic.zero_le i)
    subst i
    rw [lineCheckWithLogicalAxiom_iff]
    exact ⟨a, by simp, Or.inl ha⟩

theorem productProofGraph_project0ToPair
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p q r n : V)
    (hp : Semiformula.Evalb (M := V)
      ![p, definednessTagValue (project0PairIndexValue q r) n]
      (productProofGraph w hw).val) :
    Semiformula.Evalb (M := V)
      ![project0ToPairValue p q r n,
        definednessTagValue (pairIndexValue q r) n]
      (productProofGraph w hw).val := by
  let Th := productPRTheoryPresentation w hw
  let a := definednessTagValue (V := V) (project0PairIndexValue q r) n
  let b := definednessTagValue (V := V) (pairIndexValue q r) n
  let c := project0ToPairAxiomCodeValue (V := V) q r n
  let u := oneLineProofValue c
  have hc : Semiformula.Evalb (M := V) ![c, a, b] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hu : Semiformula.Evalb (M := V) ![u, c]
      (proofGraphWithLogicalAxiom Th productLogicalAxiomLeaf).val :=
    productProofGraph_oneLine Th c
      (productLogicalAxiomLeaf_project0ToPair q r n)
  have hm : Semiformula.Evalb (M := V)
      ![project0ToPairValue p q r n, u, p] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th productLogicalAxiomLeaf
    p a c b u (project0ToPairValue p q r n) hp hc hu hm

theorem productProofGraph_project1ToPair
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p q r n : V)
    (hp : Semiformula.Evalb (M := V)
      ![p, definednessTagValue (project1PairIndexValue q r) n]
      (productProofGraph w hw).val) :
    Semiformula.Evalb (M := V)
      ![project1ToPairValue p q r n,
        definednessTagValue (pairIndexValue q r) n]
      (productProofGraph w hw).val := by
  let Th := productPRTheoryPresentation w hw
  let a := definednessTagValue (V := V) (project1PairIndexValue q r) n
  let b := definednessTagValue (V := V) (pairIndexValue q r) n
  let c := project1ToPairAxiomCodeValue (V := V) q r n
  let u := oneLineProofValue c
  have hc : Semiformula.Evalb (M := V) ![c, a, b] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hu : Semiformula.Evalb (M := V) ![u, c]
      (proofGraphWithLogicalAxiom Th productLogicalAxiomLeaf).val :=
    productProofGraph_oneLine Th c
      (productLogicalAxiomLeaf_project1ToPair q r n)
  have hm : Semiformula.Evalb (M := V)
      ![project1ToPairValue p q r n, u, p] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th productLogicalAxiomLeaf
    p a c b u (project1ToPairValue p q r n) hp hc hu hm

theorem productProofGraph_pairToLeft
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p q r n : V)
    (hp : Semiformula.Evalb (M := V)
      ![p, definednessTagValue (pairIndexValue q r) n]
      (productProofGraph w hw).val) :
    Semiformula.Evalb (M := V)
      ![pairToLeftValue p q r n, definednessTagValue q n]
      (productProofGraph w hw).val := by
  let Th := productPRTheoryPresentation w hw
  let a := definednessTagValue (V := V) (pairIndexValue q r) n
  let b := definednessTagValue (V := V) q n
  let c := pairToLeftAxiomCodeValue (V := V) q r n
  let u := oneLineProofValue c
  have hc : Semiformula.Evalb (M := V) ![c, a, b] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hu : Semiformula.Evalb (M := V) ![u, c]
      (proofGraphWithLogicalAxiom Th productLogicalAxiomLeaf).val :=
    productProofGraph_oneLine Th c
      (productLogicalAxiomLeaf_pairToLeft q r n)
  have hm : Semiformula.Evalb (M := V)
      ![pairToLeftValue p q r n, u, p] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th productLogicalAxiomLeaf
    p a c b u (pairToLeftValue p q r n) hp hc hu hm

theorem productProofGraph_pairToRight
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p q r n : V)
    (hp : Semiformula.Evalb (M := V)
      ![p, definednessTagValue (pairIndexValue q r) n]
      (productProofGraph w hw).val) :
    Semiformula.Evalb (M := V)
      ![pairToRightValue p q r n, definednessTagValue r n]
      (productProofGraph w hw).val := by
  let Th := productPRTheoryPresentation w hw
  let a := definednessTagValue (V := V) (pairIndexValue q r) n
  let b := definednessTagValue (V := V) r n
  let c := pairToRightAxiomCodeValue (V := V) q r n
  let u := oneLineProofValue c
  have hc : Semiformula.Evalb (M := V) ![c, a, b] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hu : Semiformula.Evalb (M := V) ![u, c]
      (proofGraphWithLogicalAxiom Th productLogicalAxiomLeaf).val :=
    productProofGraph_oneLine Th c
      (productLogicalAxiomLeaf_pairToRight q r n)
  have hm : Semiformula.Evalb (M := V)
      ![pairToRightValue p q r n, u, p] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th productLogicalAxiomLeaf
    p a c b u (pairToRightValue p q r n) hp hc hu hm

theorem productProofGraph_componentsToPair
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p h q r n : V)
    (hp : Semiformula.Evalb (M := V)
      ![p, definednessTagValue q n] (productProofGraph w hw).val)
    (hh : Semiformula.Evalb (M := V)
      ![h, definednessTagValue r n] (productProofGraph w hw).val) :
    Semiformula.Evalb (M := V)
      ![componentsToPairValue p h q r n,
        definednessTagValue (pairIndexValue q r) n]
      (productProofGraph w hw).val := by
  let Th := productPRTheoryPresentation w hw
  let a := definednessTagValue (V := V) q n
  let b := definednessTagValue (V := V) r n
  let d := definednessTagValue (V := V) (pairIndexValue q r) n
  let e := impValue b d
  let c := componentsToPairAxiomCodeValue (V := V) q r n
  let u := oneLineProofValue c
  let v := mpValue u p
  have hc : Semiformula.Evalb (M := V) ![c, a, e] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have he : Semiformula.Evalb (M := V) ![e, b, d] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hu : Semiformula.Evalb (M := V) ![u, c]
      (proofGraphWithLogicalAxiom Th productLogicalAxiomLeaf).val :=
    productProofGraph_oneLine Th c
      (productLogicalAxiomLeaf_componentsToPair q r n)
  have hm₁ : Semiformula.Evalb (M := V) ![v, u, p] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  have hv : Semiformula.Evalb (M := V) ![v, e]
      (productProofGraph w hw).val :=
    proofGraphWithLogicalAxiom_of_mpGraph Th productLogicalAxiomLeaf
      p a c e u v hp hc hu hm₁
  have hm₂ : Semiformula.Evalb (M := V)
      ![componentsToPairValue p h q r n, v, h] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th productLogicalAxiomLeaf
    h b e d v (componentsToPairValue p h q r n) hh he hv hm₂

end FailureOfComposition.NumericalProductProofs
