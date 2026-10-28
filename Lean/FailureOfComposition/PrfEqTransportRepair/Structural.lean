/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.PrfEqTransportRepair.Soundness
import FailureOfComposition.NumericalProofBridge.Structural

/-!
# Structural graph and internal preservation for the transport repair

This module represents the additive transport scheme and its two-step
modus-ponens constructor inside arbitrary models of PA.  All proof codes,
program indices, formula codes, and the output proof code are internal
variables in the preservation sentence.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization
open CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition.PrfEqTransportRepair

open ConcreteEvaluator NumericalProofBridge ProofSearch

/-! ## Internal values and graphs for the new scheme -/

noncomputable def transportAxiomCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y y' d : V) : V :=
  impValue (equalityCodeValue y y')
    (impValue (equalityCodeValue y d) (equalityCodeValue y' d))

noncomputable def transportAxiomCodeGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “c y z d.
    ∃ a, !equalityCodeGraph a y z ∧
    ∃ b, !equalityCodeGraph b y d ∧
    ∃ o, !equalityCodeGraph o z d ∧
    ∃ i, !impGraph i b o ∧
      !impGraph c a i”

theorem transportAxiomCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c y y' d : V) :
    Semiformula.Evalb (M := V) ![c, y, y', d]
        transportAxiomCodeGraph.val ↔
      c = transportAxiomCodeValue y y' d := by
  simp [transportAxiomCodeGraph, transportAxiomCodeValue,
    equalityCodeGraph_iff, impGraph_iff_impValue]

theorem transportAxiomCodeValue_nat (y y' d : ℕ) :
    transportAxiomCodeValue y y' d = transportAxiomCode y y' d := by
  simp [transportAxiomCodeValue, equalityCodeValue_nat, impValue_nat,
    transportAxiomCode_eq_imp]

noncomputable def transportAxiomLeaf : 𝚺₁.Semisentence 1 := .mkSigma
  “c. ∃ y z d, !transportAxiomCodeGraph c y z d”

theorem transportAxiomLeaf_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c : V) :
    Semiformula.Evalb (M := V) ![c] transportAxiomLeaf.val ↔
      ∃ y y' d : V, c = transportAxiomCodeValue y y' d := by
  simp [transportAxiomLeaf, transportAxiomCodeGraph_iff]

noncomputable def transportRepairLogicalAxiomLeaf : 𝚺₁.Semisentence 1 :=
  extendedLogicalAxiomLeaf ⋎ transportAxiomLeaf

theorem transportRepairLogicalAxiomLeaf_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c : V) :
    Semiformula.Evalb (M := V) ![c]
        transportRepairLogicalAxiomLeaf.val ↔
      Semiformula.Evalb (M := V) ![c] extendedLogicalAxiomLeaf.val ∨
      ∃ y y' d : V, c = transportAxiomCodeValue y y' d := by
  simp [transportRepairLogicalAxiomLeaf, transportAxiomLeaf_iff]

theorem transportRepairLogicalAxiomLeaf_old
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c : V)
    (h : Semiformula.Evalb (M := V) ![c]
      extendedLogicalAxiomLeaf.val) :
    Semiformula.Evalb (M := V) ![c]
      transportRepairLogicalAxiomLeaf.val :=
  (transportRepairLogicalAxiomLeaf_iff c).mpr (Or.inl h)

theorem transportRepairLogicalAxiomLeaf_transport
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y y' d : V) :
    Semiformula.Evalb (M := V)
      ![transportAxiomCodeValue y y' d]
      transportRepairLogicalAxiomLeaf.val :=
  (transportRepairLogicalAxiomLeaf_iff _).mpr
    (Or.inr ⟨y, y', d, rfl⟩)

theorem transportRepairLogicalAxiomLeaf_nat_iff
    (w : ℕ → ℕ → Bool) (c : ℕ) :
    Semiformula.Evalb (M := ℕ) ![c]
        transportRepairLogicalAxiomLeaf.val ↔
      (transportRepairTheoryPresentation w).syn.logicalAxiom.Holds
        (decodeFormula c) := by
  rw [transportRepairLogicalAxiomLeaf_iff,
    extendedLogicalAxiomLeaf_nat_iff w]
  simp only [transportAxiomCodeValue_nat]
  change
    (extendedLogicalAxiomTest (decodeFormula c) = true ∨
      ∃ y y' d, c = transportAxiomCode y y' d) ↔
    transportRepairLogicalAxiomTest (decodeFormula c) = true
  rw [extendedLogicalAxiomTest_eq_true_iff,
    transportRepairLogicalAxiomTest_eq_true_iff]
  unfold TransportRepairLogicalAxiomShape
  rw [transportAxiomShape_iff]
  have hcode (t : FormulaString) :
      c = encodeFormula t ↔ decodeFormula c = t := by
    constructor
    · rintro rfl
      exact decodeFormula_encodeFormula t
    · intro h
      calc
        c = encodeFormula (decodeFormula c) :=
          (encodeFormula_decodeFormula c).symm
        _ = encodeFormula t := by rw [h]
  simp only [transportAxiomCode, hcode]

noncomputable def transportRepairProofGraph
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝚺₁.Semisentence 2 :=
  proofGraphWithLogicalAxiom
    (transportRepairPRTheoryPresentation w hw)
    transportRepairLogicalAxiomLeaf

theorem transportRepairProofGraph_nat_iff
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p a : ℕ) :
    Semiformula.Evalb (M := ℕ) ![p, a]
        (transportRepairProofGraph w hw).val ↔
      Proof_T (transportRepairTheoryPresentation w) p a := by
  exact proofGraphWithLogicalAxiom_nat_iff
    (transportRepairPRTheoryPresentation w hw)
    transportRepairLogicalAxiomLeaf
    (transportRepairLogicalAxiomLeaf_nat_iff w) p a

/-! ## The exact transport graph -/

noncomputable def transportValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (e p y y' d : V) : V :=
  mpValue
    (mpValue (oneLineProofValue (transportAxiomCodeValue y y' d)) e) p

noncomputable def transportGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “t e p y z d.
    ∃ c, !transportAxiomCodeGraph c y z d ∧
    ∃ u, !oneLineProofGraph u c ∧
    ∃ v, !mpGraph v u e ∧
      !mpGraph t v p”

theorem transportGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (t e p y y' d : V) :
    Semiformula.Evalb (M := V) ![t, e, p, y, y', d]
        transportGraph.val ↔
      t = transportValue e p y y' d := by
  simp [transportGraph, transportValue, transportAxiomCodeGraph_iff,
    oneLineProofGraph_iff, mpGraph_iff_mpValue]

theorem transportGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (e p y y' d : V) :
    ∃ t : V, Semiformula.Evalb (M := V) ![t, e, p, y, y', d]
      transportGraph.val :=
  ⟨transportValue e p y y' d,
    (transportGraph_iff _ _ _ _ _ _).mpr rfl⟩

theorem transportGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {t u e p y y' d : V}
    (ht : Semiformula.Evalb (M := V) ![t, e, p, y, y', d]
      transportGraph.val)
    (hu : Semiformula.Evalb (M := V) ![u, e, p, y, y', d]
      transportGraph.val) :
    t = u :=
  (transportGraph_iff t e p y y' d).mp ht |>.trans
    ((transportGraph_iff u e p y y' d).mp hu).symm

theorem transportValue_nat (e p y y' d : ℕ) :
    transportValue e p y y' d = transport e p y y' d := by
  simp [transportValue, transport, oneLineProofValue_nat,
    transportAxiomCodeValue_nat, mpValue_nat]

/-! ## Internal preservation of repaired proofs -/

theorem transportRepairProofGraph_oneLine
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Th : PRTheoryPresentation) (a : V)
    (ha : Semiformula.Evalb (M := V) ![a]
      transportRepairLogicalAxiomLeaf.val) :
    Semiformula.Evalb (M := V) ![oneLineProofValue a, a]
      (proofGraphWithLogicalAxiom Th
        transportRepairLogicalAxiomLeaf).val := by
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

theorem transportRepairProofGraph_transport
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (e p y y' d : V)
    (he : Semiformula.Evalb (M := V)
      ![e, equalityCodeValue y y']
      (transportRepairProofGraph w hw).val)
    (hp : Semiformula.Evalb (M := V)
      ![p, equalityCodeValue y d]
      (transportRepairProofGraph w hw).val) :
    Semiformula.Evalb (M := V)
      ![transportValue e p y y' d, equalityCodeValue y' d]
      (transportRepairProofGraph w hw).val := by
  let Th := transportRepairPRTheoryPresentation w hw
  let a := equalityCodeValue (V := V) y y'
  let b := equalityCodeValue (V := V) y d
  let o := equalityCodeValue (V := V) y' d
  let i := impValue b o
  let c := transportAxiomCodeValue (V := V) y y' d
  let u := oneLineProofValue c
  let v := mpValue u e
  have hc : Semiformula.Evalb (M := V) ![c, a, i] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hi : Semiformula.Evalb (M := V) ![i, b, o] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hu : Semiformula.Evalb (M := V) ![u, c]
      (proofGraphWithLogicalAxiom Th
        transportRepairLogicalAxiomLeaf).val :=
    transportRepairProofGraph_oneLine Th c
      (transportRepairLogicalAxiomLeaf_transport y y' d)
  have hm₁ : Semiformula.Evalb (M := V) ![v, u, e] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  have hv : Semiformula.Evalb (M := V) ![v, i]
      (transportRepairProofGraph w hw).val :=
    proofGraphWithLogicalAxiom_of_mpGraph Th
      transportRepairLogicalAxiomLeaf e a c i u v he hc hu hm₁
  have hm₂ : Semiformula.Evalb (M := V)
      ![transportValue e p y y' d, v, p] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th
    transportRepairLogicalAxiomLeaf p b i o v
      (transportValue e p y y' d) hp hi hv hm₂

/-! ## The universally closed preservation sentence -/

noncomputable def transportPreservationMatrix
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSemisentence 9 :=
  let prf := transportRepairProofGraph w hw
  “e p y z d a b c t.
    !equalityCodeGraph a y z ∧
    !equalityCodeGraph b y d ∧
    !equalityCodeGraph c z d ∧
    !prf e a ∧
    !prf p b ∧
    !transportGraph t e p y z d →
    !prf t c”

noncomputable def uniformTransportPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSentence :=
  ∀¹* transportPreservationMatrix w hw

theorem models_uniformTransportPreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    V↓[ℒₒᵣ] ⊧ uniformTransportPreservation w hw := by
  rw [models_iff, uniformTransportPreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v =
      ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8] := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  simp only [transportPreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons'', Matrix.comp₀,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one]
  intro h
  have ha := (equalityCodeGraph_iff (v 5) (v 2) (v 3)).mp h.1
  have hb := (equalityCodeGraph_iff (v 6) (v 2) (v 4)).mp h.2.1
  have hc := (equalityCodeGraph_iff (v 7) (v 3) (v 4)).mp h.2.2.1
  have ht := (transportGraph_iff
    (v 8) (v 0) (v 1) (v 2) (v 3) (v 4)).mp h.2.2.2.2.2
  have he : Semiformula.Evalb (M := V)
      ![v 0, equalityCodeValue (v 2) (v 3)]
      (transportRepairProofGraph w hw).val := by
    simpa [ha] using h.2.2.2.1
  have hp : Semiformula.Evalb (M := V)
      ![v 1, equalityCodeValue (v 2) (v 4)]
      (transportRepairProofGraph w hw).val := by
    simpa [hb] using h.2.2.2.2.1
  have hout := transportRepairProofGraph_transport w hw
    (v 0) (v 1) (v 2) (v 3) (v 4) he hp
  simpa [ht, hc] using hout

theorem provable_PA_uniformTransportPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝗣𝗔 ⊢ uniformTransportPreservation w hw :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ =>
    models_uniformTransportPreservation (V := V) w hw

end FailureOfComposition.PrfEqTransportRepair
