/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalProofBridge.Structural.Base

/-!
# Arithmetic graphs of the numerical proof bridge maps
-/

set_option autoImplicit false
open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural
open Arith.Feferman.Specialization
open CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition.NumericalProofBridge

open ProofSearch ConcreteEvaluator

private theorem eval_select_axiom_five_iff
    {V : Type*} [ORingStructure V]
    (phi : ArithmeticSemisentence 5)
    (x y p s q n m : V) :
    Semiformula.Eval
        (Semiterm.val ![x, y, p, s, q, n, m] Empty.elim ∘
          ![(#0 : ArithmeticSemiterm Empty 7), #4, #5, #6, #3])
        Empty.elim phi ↔
      Semiformula.Evalb (M := V) ![x, q, n, m, s] phi := by
  apply Iff.of_eq
  congr 2
  funext j
  fin_cases j <;> rfl

noncomputable def bridgeEqualityValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (p s q r : V) : V :=
  mpValue (oneLineProofValue (bridgeEqualityAxiomCodeValue q r s)) p

noncomputable def bridgeLeftValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (p s q n m : V) : V :=
  mpValue (oneLineProofValue (bridgeLeftAxiomCodeValue q n m s)) p

noncomputable def bridgeRightValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (p s r n m : V) : V :=
  mpValue (oneLineProofValue (bridgeRightAxiomCodeValue r n m s)) p

noncomputable def bridgeEqualityGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “y p s q r.
    ∃ c, !bridgeEqualityAxiomCodeGraph c q r s ∧
    ∃ u, !oneLineProofGraph u c ∧
      !mpGraph y u p”

noncomputable def bridgeLeftGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “y p s q n m.
    ∃ c, !bridgeLeftAxiomCodeGraph c q n m s ∧
    ∃ u, !oneLineProofGraph u c ∧
      !mpGraph y u p”

noncomputable def bridgeRightGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “y p s r n m.
    ∃ c, !bridgeRightAxiomCodeGraph c r n m s ∧
    ∃ u, !oneLineProofGraph u c ∧
      !mpGraph y u p”

theorem bridgeEqualityGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y p s q r : V) :
    Semiformula.Evalb (M := V) ![y, p, s, q, r]
        bridgeEqualityGraph.val ↔
      y = bridgeEqualityValue p s q r := by
  simp [bridgeEqualityGraph, bridgeEqualityValue,
    bridgeEqualityAxiomCodeGraph_iff, oneLineProofGraph_iff,
    mpGraph_iff_mpValue]

theorem bridgeLeftGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y p s q n m : V) :
    Semiformula.Evalb (M := V) ![y, p, s, q, n, m]
        bridgeLeftGraph.val ↔
      y = bridgeLeftValue p s q n m := by
  simp [bridgeLeftGraph, bridgeLeftValue,
    eval_select_axiom_five_iff, bridgeLeftAxiomCodeGraph_iff,
    oneLineProofGraph_iff,
    mpGraph_iff_mpValue]

theorem bridgeRightGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y p s r n m : V) :
    Semiformula.Evalb (M := V) ![y, p, s, r, n, m]
        bridgeRightGraph.val ↔
      y = bridgeRightValue p s r n m := by
  simp [bridgeRightGraph, bridgeRightValue,
    eval_select_axiom_five_iff, bridgeRightAxiomCodeGraph_iff,
    oneLineProofGraph_iff,
    mpGraph_iff_mpValue]

theorem bridgeEqualityValue_nat (p s q r : ℕ) :
    bridgeEqualityValue p s q r = bridgeEquality p s q r := by
  simp [bridgeEqualityValue, bridgeEquality, oneLineProofValue_nat,
    bridgeEqualityAxiomCodeValue_nat, mpValue_nat]

theorem bridgeLeftValue_nat (p s q n m : ℕ) :
    bridgeLeftValue p s q n m = bridgeLeft p s q n m := by
  simp [bridgeLeftValue, bridgeLeft, oneLineProofValue_nat,
    bridgeLeftAxiomCodeValue_nat, mpValue_nat]

theorem bridgeRightValue_nat (p s r n m : ℕ) :
    bridgeRightValue p s r n m = bridgeRight p s r n m := by
  simp [bridgeRightValue, bridgeRight, oneLineProofValue_nat,
    bridgeRightAxiomCodeValue_nat, mpValue_nat]

theorem extendedProofGraph_oneLine
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (Th : PRTheoryPresentation) (a : V)
    (ha : Semiformula.Evalb (M := V) ![a]
      extendedLogicalAxiomLeaf.val) :
    Semiformula.Evalb (M := V) ![oneLineProofValue a, a]
      (proofGraphWithLogicalAxiom Th extendedLogicalAxiomLeaf).val := by
  rw [proofGraphWithLogicalAxiom_iff]
  have hdecode : listDecodeValue (oneLineProofValue a) = a ∷ (0 : V) := by
    exact listDecodeValue_leftInverse (a ∷ (0 : V))
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

theorem extendedProofGraph_of_bridgeEqualityGraph
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p s q r a u e b : V)
    (ha : Semiformula.Evalb (M := V) ![a, q, r]
      eqSentenceCodeGraph.val)
    (hu : Semiformula.Evalb (M := V) ![u, a, s] stageCodeGraph.val)
    (he : Semiformula.Evalb (M := V) ![e, q, r] equalityCodeGraph.val)
    (hp : Semiformula.Evalb (M := V) ![p, u]
      (extendedProofGraph w hw).val)
    (hb : Semiformula.Evalb (M := V) ![b, p, s, q, r]
      bridgeEqualityGraph.val) :
    Semiformula.Evalb (M := V) ![b, e]
      (extendedProofGraph w hw).val := by
  have haq := (eqSentenceCodeGraph_iff a q r).mp ha
  have huq := (stageCodeGraph_iff u a s).mp hu
  have heq := (equalityCodeGraph_iff e q r).mp he
  have hbq := (bridgeEqualityGraph_iff b p s q r).mp hb
  subst a
  subst u
  subst e
  subst b
  let Th := extendedPRTheoryPresentation w hw
  let c := bridgeEqualityAxiomCodeValue (V := V) q r s
  let v := oneLineProofValue c
  have hc : Semiformula.Evalb (M := V)
      ![c, stageCodeValue (eqSentenceCodeValue q r) s,
        equalityCodeValue q r] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hv : Semiformula.Evalb (M := V) ![v, c]
      (proofGraphWithLogicalAxiom Th extendedLogicalAxiomLeaf).val :=
    extendedProofGraph_oneLine Th c
      (extendedLogicalAxiomLeaf_bridgeEquality q r s)
  have hmp : Semiformula.Evalb (M := V)
      ![bridgeEqualityValue p s q r, v, p] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th extendedLogicalAxiomLeaf
    p (stageCodeValue (eqSentenceCodeValue q r) s) c
    (equalityCodeValue q r) v (bridgeEqualityValue p s q r)
    hp hc hv hmp

theorem extendedProofGraph_of_bridgeLeftGraph
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p s q n m a u f b : V)
    (ha : Semiformula.Evalb (M := V) ![a, q, n, m]
      leftSentenceCodeGraph.val)
    (hu : Semiformula.Evalb (M := V) ![u, a, s] stageCodeGraph.val)
    (hf : Semiformula.Evalb (M := V) ![f, q, n, m]
      leftInstanceCodeGraph.val)
    (hp : Semiformula.Evalb (M := V) ![p, u]
      (extendedProofGraph w hw).val)
    (hb : Semiformula.Evalb (M := V) ![b, p, s, q, n, m]
      bridgeLeftGraph.val) :
    Semiformula.Evalb (M := V) ![b, f]
      (extendedProofGraph w hw).val := by
  have haq := (leftSentenceCodeGraph_iff a q n m).mp ha
  have huq := (stageCodeGraph_iff u a s).mp hu
  have hfq := (leftInstanceCodeGraph_iff f q n m).mp hf
  have hbq := (bridgeLeftGraph_iff b p s q n m).mp hb
  subst a
  subst u
  subst f
  subst b
  let Th := extendedPRTheoryPresentation w hw
  let c := bridgeLeftAxiomCodeValue (V := V) q n m s
  let v := oneLineProofValue c
  have hc : Semiformula.Evalb (M := V)
      ![c, stageCodeValue (leftSentenceCodeValue q n m) s,
        leftInstanceCodeValue q n m] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hv : Semiformula.Evalb (M := V) ![v, c]
      (proofGraphWithLogicalAxiom Th extendedLogicalAxiomLeaf).val :=
    extendedProofGraph_oneLine Th c
      (extendedLogicalAxiomLeaf_bridgeLeft q n m s)
  have hmp : Semiformula.Evalb (M := V)
      ![bridgeLeftValue p s q n m, v, p] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th extendedLogicalAxiomLeaf
    p (stageCodeValue (leftSentenceCodeValue q n m) s) c
    (leftInstanceCodeValue q n m) v (bridgeLeftValue p s q n m)
    hp hc hv hmp

theorem extendedProofGraph_of_bridgeRightGraph
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p s r n m a u g b : V)
    (ha : Semiformula.Evalb (M := V) ![a, r, n, m]
      rightSentenceCodeGraph.val)
    (hu : Semiformula.Evalb (M := V) ![u, a, s] stageCodeGraph.val)
    (hg : Semiformula.Evalb (M := V) ![g, r, n, m]
      rightInstanceCodeGraph.val)
    (hp : Semiformula.Evalb (M := V) ![p, u]
      (extendedProofGraph w hw).val)
    (hb : Semiformula.Evalb (M := V) ![b, p, s, r, n, m]
      bridgeRightGraph.val) :
    Semiformula.Evalb (M := V) ![b, g]
      (extendedProofGraph w hw).val := by
  have haq := (rightSentenceCodeGraph_iff a r n m).mp ha
  have huq := (stageCodeGraph_iff u a s).mp hu
  have hgq := (rightInstanceCodeGraph_iff g r n m).mp hg
  have hbq := (bridgeRightGraph_iff b p s r n m).mp hb
  subst a
  subst u
  subst g
  subst b
  let Th := extendedPRTheoryPresentation w hw
  let c := bridgeRightAxiomCodeValue (V := V) r n m s
  let v := oneLineProofValue c
  have hc : Semiformula.Evalb (M := V)
      ![c, stageCodeValue (rightSentenceCodeValue r n m) s,
        rightInstanceCodeValue r n m] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hv : Semiformula.Evalb (M := V) ![v, c]
      (proofGraphWithLogicalAxiom Th extendedLogicalAxiomLeaf).val :=
    extendedProofGraph_oneLine Th c
      (extendedLogicalAxiomLeaf_bridgeRight r n m s)
  have hmp : Semiformula.Evalb (M := V)
      ![bridgeRightValue p s r n m, v, p] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th extendedLogicalAxiomLeaf
    p (stageCodeValue (rightSentenceCodeValue r n m) s) c
    (rightInstanceCodeValue r n m) v (bridgeRightValue p s r n m)
    hp hc hv hmp

end FailureOfComposition.NumericalProofBridge
