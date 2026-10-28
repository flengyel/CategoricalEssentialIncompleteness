/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalExtensionComposition.Structural.Maps

/-!
# PA-internal preservation by the composed B1(7) proof maps

The four closed sentences below quantify the supplied proof codes, program
indices, inputs and outputs, intermediate formula codes, and result proof
codes inside arithmetic.  Their proofs work in every model of PA and use the
common structural proof graph; they do not appeal to an external choice of a
standard computation witness.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalExtensionComposition

open FiniteExtensionChecker NumericalExtensionProofs NumericalProductProofs

noncomputable section

def projectionEqualityToPairPreservationMatrix
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSemisentence 13 :=
  let prf := extensionCompositionProofGraph w hw
  “u p q r t i j k e g dJ dP z.
    !project1PairIndexGraph j q r ∧
    !pairIndexGraph k q r ∧
    !equalityCodeGraph e j r ∧
    !rightInstanceCodeGraph g r t i ∧
    !definednessTagGraph dJ j t ∧
    !definednessTagGraph dP k t ∧
    !prf u e ∧
    !prf p g ∧
    !projectionEqualityToPairGraph z u p q r t i →
    !prf z dP”

def projectionEqualityToLeftPreservationMatrix
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSemisentence 13 :=
  let prf := extensionCompositionProofGraph w hw
  “u p q r t i j k e g dP dL z.
    !project1PairIndexGraph j q r ∧
    !pairIndexGraph k q r ∧
    !equalityCodeGraph e j r ∧
    !rightInstanceCodeGraph g r t i ∧
    !definednessTagGraph dP k t ∧
    !definednessTagGraph dL q t ∧
    !prf u e ∧
    !prf p g ∧
    !projectionEqualityToLeftGraph z u p q r t i →
    !prf z dL”

def componentValuesToCheckerPreservationMatrix
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSemisentence 15 :=
  let prf := extensionCompositionProofGraph w hw
  “v a b q r t c i p j e f g d z.
    !pairIndexGraph p q r ∧
    !compIndexGraph j ↑extensionCheckerIndex p ∧
    !equalityCodeGraph e j p ∧
    !rightInstanceCodeGraph f q t c ∧
    !rightInstanceCodeGraph g r t i ∧
    !checkerInstanceCodeGraph d c i ∧
    !prf v e ∧
    !prf a f ∧
    !prf b g ∧
    !componentValuesToCheckerGraph z v a b q r t c i →
    !prf z d”

def componentValuesToExtPreservationMatrix
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSemisentence 16 :=
  let prf := extensionCompositionProofGraph w hw
  “v a b q r t c i p j e f g d x z.
    !pairIndexGraph p q r ∧
    !compIndexGraph j ↑extensionCheckerIndex p ∧
    !equalityCodeGraph e j p ∧
    !rightInstanceCodeGraph f q t c ∧
    !rightInstanceCodeGraph g r t i ∧
    !checkerInstanceCodeGraph d c i ∧
    !extensionInstanceCodeGraph x c i ∧
    !prf v e ∧
    !prf a f ∧
    !prf b g ∧
    !componentValuesToExtGraph z v a b q r t c i →
    !prf z x”

def uniformProjectionEqualityToPairPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSentence :=
  ∀¹* projectionEqualityToPairPreservationMatrix w hw

def uniformProjectionEqualityToLeftPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSentence :=
  ∀¹* projectionEqualityToLeftPreservationMatrix w hw

def uniformComponentValuesToCheckerPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSentence :=
  ∀¹* componentValuesToCheckerPreservationMatrix w hw

def uniformComponentValuesToExtPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSentence :=
  ∀¹* componentValuesToExtPreservationMatrix w hw

theorem models_uniformProjectionEqualityToPairPreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    V↓[ℒₒᵣ] ⊧ uniformProjectionEqualityToPairPreservation w hw := by
  rw [models_iff, uniformProjectionEqualityToPairPreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v =
      ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9,
        v 10, v 11, v 12] := by
    ext j
    fin_cases j <;> rfl
  rw [hv]
  simp only [projectionEqualityToPairPreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons'', Matrix.comp₀,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one]
  rintro ⟨hj, hk, he, hg, -, hdP, hu, hp, hz⟩
  have hj' := (project1PairIndexGraph_iff (v 6) (v 2) (v 3)).mp hj
  have hk' := (pairIndexGraph_iff (v 7) (v 2) (v 3)).mp hk
  have he' := (equalityCodeGraph_iff (v 8) (v 6) (v 3)).mp he
  have hg' := (rightInstanceCodeGraph_iff
    (v 9) (v 3) (v 4) (v 5)).mp hg
  have hdP' := (definednessTagGraph_iff
    (v 11) (v 7) (v 4)).mp hdP
  have hz' := (projectionEqualityToPairGraph_iff
    (v 12) (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)).mp hz
  have hu' : Semiformula.Evalb (M := V)
      ![v 0, equalityCodeValue (project1PairIndexValue (v 2) (v 3)) (v 3)]
      (extensionCompositionProofGraph w hw).val := by
    simpa [he', hj'] using hu
  have hp' : Semiformula.Evalb (M := V)
      ![v 1, rightInstanceCodeValue (v 3) (v 4) (v 5)]
      (extensionCompositionProofGraph w hw).val := by
    simpa [hg'] using hp
  have hout := extensionCompositionProofGraph_projectionEqualityToPair
    w hw (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) hu' hp'
  simpa [hz', hdP', hk'] using hout

theorem models_uniformProjectionEqualityToLeftPreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    V↓[ℒₒᵣ] ⊧ uniformProjectionEqualityToLeftPreservation w hw := by
  rw [models_iff, uniformProjectionEqualityToLeftPreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v =
      ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9,
        v 10, v 11, v 12] := by
    ext j
    fin_cases j <;> rfl
  rw [hv]
  simp only [projectionEqualityToLeftPreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons'', Matrix.comp₀,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one]
  rintro ⟨hj, -, he, hg, -, hdL, hu, hp, hz⟩
  have hj' := (project1PairIndexGraph_iff (v 6) (v 2) (v 3)).mp hj
  have he' := (equalityCodeGraph_iff (v 8) (v 6) (v 3)).mp he
  have hg' := (rightInstanceCodeGraph_iff
    (v 9) (v 3) (v 4) (v 5)).mp hg
  have hdL' := (definednessTagGraph_iff (v 11) (v 2) (v 4)).mp hdL
  have hz' := (projectionEqualityToLeftGraph_iff
    (v 12) (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)).mp hz
  have hu' : Semiformula.Evalb (M := V)
      ![v 0, equalityCodeValue (project1PairIndexValue (v 2) (v 3)) (v 3)]
      (extensionCompositionProofGraph w hw).val := by
    simpa [he', hj'] using hu
  have hp' : Semiformula.Evalb (M := V)
      ![v 1, rightInstanceCodeValue (v 3) (v 4) (v 5)]
      (extensionCompositionProofGraph w hw).val := by
    simpa [hg'] using hp
  have hout := extensionCompositionProofGraph_projectionEqualityToLeft
    w hw (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) hu' hp'
  simpa [hz', hdL'] using hout

theorem models_uniformComponentValuesToCheckerPreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    V↓[ℒₒᵣ] ⊧ uniformComponentValuesToCheckerPreservation w hw := by
  rw [models_iff, uniformComponentValuesToCheckerPreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v =
      ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9,
        v 10, v 11, v 12, v 13, v 14] := by
    ext j
    fin_cases j <;> rfl
  rw [hv]
  simp only [componentValuesToCheckerPreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons'', Matrix.comp₀,
    Semiterm.val_bvar, Semiterm.val_operator,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Tarski.Structure.numeral_eq_numeral]
  rintro ⟨hp, hj, he, hf, hg, hd, hvProof, haProof, hbProof, hz⟩
  have hp' := (pairIndexGraph_iff (v 8) (v 3) (v 4)).mp hp
  have hj' := (compIndexGraph_iff
    (v 9) (ORingStructure.numeral extensionCheckerIndex) (v 8)).mp hj
  have he' := (equalityCodeGraph_iff (v 10) (v 9) (v 8)).mp he
  have hf' := (rightInstanceCodeGraph_iff
    (v 11) (v 3) (v 5) (v 6)).mp hf
  have hg' := (rightInstanceCodeGraph_iff
    (v 12) (v 4) (v 5) (v 7)).mp hg
  have hd' := (checkerInstanceCodeGraph_iff (v 13) (v 6) (v 7)).mp hd
  have hz' := (componentValuesToCheckerGraph_iff
    (v 14) (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)).mp hz
  have hv' : Semiformula.Evalb (M := V)
      ![v 0, equalityCodeValue
        (compIndexValue (ORingStructure.numeral extensionCheckerIndex)
          (pairIndexValue (v 3) (v 4)))
        (pairIndexValue (v 3) (v 4))]
      (extensionCompositionProofGraph w hw).val := by
    simpa [he', hj', hp'] using hvProof
  have ha' : Semiformula.Evalb (M := V)
      ![v 1, rightInstanceCodeValue (v 3) (v 5) (v 6)]
      (extensionCompositionProofGraph w hw).val := by
    simpa [hf'] using haProof
  have hb' : Semiformula.Evalb (M := V)
      ![v 2, rightInstanceCodeValue (v 4) (v 5) (v 7)]
      (extensionCompositionProofGraph w hw).val := by
    simpa [hg'] using hbProof
  have hout := extensionCompositionProofGraph_componentValuesToChecker
    w hw (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)
      hv' ha' hb'
  simpa [hz', hd'] using hout

theorem models_uniformComponentValuesToExtPreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    V↓[ℒₒᵣ] ⊧ uniformComponentValuesToExtPreservation w hw := by
  rw [models_iff, uniformComponentValuesToExtPreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v =
      ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9,
        v 10, v 11, v 12, v 13, v 14, v 15] := by
    ext j
    fin_cases j <;> rfl
  rw [hv]
  simp only [componentValuesToExtPreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons'', Matrix.comp₀,
    Semiterm.val_bvar, Semiterm.val_operator,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Tarski.Structure.numeral_eq_numeral]
  rintro ⟨hp, hj, he, hf, hg, -, hx, hvProof, haProof, hbProof, hz⟩
  have hp' := (pairIndexGraph_iff (v 8) (v 3) (v 4)).mp hp
  have hj' := (compIndexGraph_iff
    (v 9) (ORingStructure.numeral extensionCheckerIndex) (v 8)).mp hj
  have he' := (equalityCodeGraph_iff (v 10) (v 9) (v 8)).mp he
  have hf' := (rightInstanceCodeGraph_iff
    (v 11) (v 3) (v 5) (v 6)).mp hf
  have hg' := (rightInstanceCodeGraph_iff
    (v 12) (v 4) (v 5) (v 7)).mp hg
  have hx' := (extensionInstanceCodeGraph_iff (v 14) (v 6) (v 7)).mp hx
  have hz' := (componentValuesToExtGraph_iff
    (v 15) (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)).mp hz
  have hv' : Semiformula.Evalb (M := V)
      ![v 0, equalityCodeValue
        (compIndexValue (ORingStructure.numeral extensionCheckerIndex)
          (pairIndexValue (v 3) (v 4)))
        (pairIndexValue (v 3) (v 4))]
      (extensionCompositionProofGraph w hw).val := by
    simpa [he', hj', hp'] using hvProof
  have ha' : Semiformula.Evalb (M := V)
      ![v 1, rightInstanceCodeValue (v 3) (v 5) (v 6)]
      (extensionCompositionProofGraph w hw).val := by
    simpa [hf'] using haProof
  have hb' : Semiformula.Evalb (M := V)
      ![v 2, rightInstanceCodeValue (v 4) (v 5) (v 7)]
      (extensionCompositionProofGraph w hw).val := by
    simpa [hg'] using hbProof
  have hout := extensionCompositionProofGraph_componentValuesToExt
    w hw (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)
      hv' ha' hb'
  simpa [hz', hx'] using hout

theorem provable_PA_uniformProjectionEqualityToPairPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝗣𝗔 ⊢ uniformProjectionEqualityToPairPreservation w hw :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ =>
    models_uniformProjectionEqualityToPairPreservation (V := V) w hw

theorem provable_PA_uniformProjectionEqualityToLeftPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝗣𝗔 ⊢ uniformProjectionEqualityToLeftPreservation w hw :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ =>
    models_uniformProjectionEqualityToLeftPreservation (V := V) w hw

theorem provable_PA_uniformComponentValuesToCheckerPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝗣𝗔 ⊢ uniformComponentValuesToCheckerPreservation w hw :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ =>
    models_uniformComponentValuesToCheckerPreservation (V := V) w hw

theorem provable_PA_uniformComponentValuesToExtPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝗣𝗔 ⊢ uniformComponentValuesToExtPreservation w hw :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ =>
    models_uniformComponentValuesToExtPreservation (V := V) w hw

end

end FailureOfComposition.NumericalExtensionComposition
