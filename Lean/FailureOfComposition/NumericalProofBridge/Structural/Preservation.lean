/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalProofBridge.Structural.BridgeMaps

/-!
# Uniform PA preservation of the numerical proof bridge maps
-/

@[expose] public section

set_option autoImplicit false
open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural
open Arith.Feferman.Specialization
open CategoricalRiceShapiro.Evaluator
open FailureOfComposition.NumericalSpecialization

namespace FailureOfComposition.NumericalProofBridge

open ProofSearch ConcreteEvaluator

noncomputable def equalityBridgePreservationMatrix
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSemisentence 8 :=
  let prf := extendedProofGraph w hw
  “p s q r a u e b.
    !eqSentenceCodeGraph a q r ∧
    !stageCodeGraph u a s ∧
    !equalityCodeGraph e q r ∧
    !prf p u ∧
    !bridgeEqualityGraph b p s q r →
    !prf b e”

noncomputable def leftBridgePreservationMatrix
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSemisentence 9 :=
  let prf := extendedProofGraph w hw
  “p s q n m a u f b.
    !leftSentenceCodeGraph a q n m ∧
    !stageCodeGraph u a s ∧
    !leftInstanceCodeGraph f q n m ∧
    !prf p u ∧
    !bridgeLeftGraph b p s q n m →
    !prf b f”

noncomputable def rightBridgePreservationMatrix
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSemisentence 9 :=
  let prf := extendedProofGraph w hw
  “p s r n m a u g b.
    !rightSentenceCodeGraph a r n m ∧
    !stageCodeGraph u a s ∧
    !rightInstanceCodeGraph g r n m ∧
    !prf p u ∧
    !bridgeRightGraph b p s r n m →
    !prf b g”

noncomputable def uniformEqualityBridgePreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSentence :=
  ∀¹* equalityBridgePreservationMatrix w hw

noncomputable def uniformLeftBridgePreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSentence :=
  ∀¹* leftBridgePreservationMatrix w hw

noncomputable def uniformRightBridgePreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSentence :=
  ∀¹* rightBridgePreservationMatrix w hw

theorem models_uniformEqualityBridgePreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    V↓[ℒₒᵣ] ⊧ uniformEqualityBridgePreservation w hw := by
  rw [models_iff, uniformEqualityBridgePreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7] := by
    ext j
    fin_cases j <;> rfl
  rw [hv]
  simp only [equalityBridgePreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons'', Matrix.comp₀,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one]
  intro h
  exact extendedProofGraph_of_bridgeEqualityGraph w hw
    (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem models_uniformLeftBridgePreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    V↓[ℒₒᵣ] ⊧ uniformLeftBridgePreservation w hw := by
  rw [models_iff, uniformLeftBridgePreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v =
      ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8] := by
    ext j
    fin_cases j <;> rfl
  rw [hv]
  simp only [leftBridgePreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons'', Matrix.comp₀,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one]
  intro h
  exact extendedProofGraph_of_bridgeLeftGraph w hw
    (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem models_uniformRightBridgePreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    V↓[ℒₒᵣ] ⊧ uniformRightBridgePreservation w hw := by
  rw [models_iff, uniformRightBridgePreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v =
      ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8] := by
    ext j
    fin_cases j <;> rfl
  rw [hv]
  simp only [rightBridgePreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons'', Matrix.comp₀,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one]
  intro h
  exact extendedProofGraph_of_bridgeRightGraph w hw
    (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem provable_PA_uniformEqualityBridgePreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝗣𝗔 ⊢ uniformEqualityBridgePreservation w hw :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ =>
    models_uniformEqualityBridgePreservation (V := V) w hw

theorem provable_PA_uniformLeftBridgePreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝗣𝗔 ⊢ uniformLeftBridgePreservation w hw :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ =>
    models_uniformLeftBridgePreservation (V := V) w hw

theorem provable_PA_uniformRightBridgePreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝗣𝗔 ⊢ uniformRightBridgePreservation w hw :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ =>
    models_uniformRightBridgePreservation (V := V) w hw

theorem provable_PA_paEqualityBridgePreservation :
    𝗣𝗔 ⊢ uniformEqualityBridgePreservation
      paStageWitness primrec_paStageWitness :=
  provable_PA_uniformEqualityBridgePreservation
    paStageWitness primrec_paStageWitness

theorem provable_PA_paLeftBridgePreservation :
    𝗣𝗔 ⊢ uniformLeftBridgePreservation
      paStageWitness primrec_paStageWitness :=
  provable_PA_uniformLeftBridgePreservation
    paStageWitness primrec_paStageWitness

theorem provable_PA_paRightBridgePreservation :
    𝗣𝗔 ⊢ uniformRightBridgePreservation
      paStageWitness primrec_paStageWitness :=
  provable_PA_uniformRightBridgePreservation
    paStageWitness primrec_paStageWitness

end FailureOfComposition.NumericalProofBridge
