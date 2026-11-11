/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalProductProofs.Structural.Maps

/-!
# PA-internal preservation by the product proof maps

The five sentences below universally quantify all program indices, formula
codes, proof codes, and map outputs.  Thus their content includes nonstandard
elements in every model of PA.  Their proofs use the structural proof graph,
not external computation on standard natural numbers.
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

noncomputable def project0ToPairPreservationMatrix
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSemisentence 9 :=
  let prf := productProofGraph w hw
  “p q r n j k a b t.
    !project0PairIndexGraph j q r ∧
    !pairIndexGraph k q r ∧
    !definednessTagGraph a j n ∧
    !definednessTagGraph b k n ∧
    !prf p a ∧
    !project0ToPairGraph t p q r n →
    !prf t b”

noncomputable def project1ToPairPreservationMatrix
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSemisentence 9 :=
  let prf := productProofGraph w hw
  “p q r n j k a b t.
    !project1PairIndexGraph j q r ∧
    !pairIndexGraph k q r ∧
    !definednessTagGraph a j n ∧
    !definednessTagGraph b k n ∧
    !prf p a ∧
    !project1ToPairGraph t p q r n →
    !prf t b”

noncomputable def pairToLeftPreservationMatrix
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSemisentence 8 :=
  let prf := productProofGraph w hw
  “p q r n k a b t.
    !pairIndexGraph k q r ∧
    !definednessTagGraph a k n ∧
    !definednessTagGraph b q n ∧
    !prf p a ∧
    !pairToLeftGraph t p q r n →
    !prf t b”

noncomputable def pairToRightPreservationMatrix
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSemisentence 8 :=
  let prf := productProofGraph w hw
  “p q r n k a b t.
    !pairIndexGraph k q r ∧
    !definednessTagGraph a k n ∧
    !definednessTagGraph b r n ∧
    !prf p a ∧
    !pairToRightGraph t p q r n →
    !prf t b”

noncomputable def componentsToPairPreservationMatrix
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSemisentence 10 :=
  let prf := productProofGraph w hw
  “p h q r n k a b c t.
    !pairIndexGraph k q r ∧
    !definednessTagGraph a q n ∧
    !definednessTagGraph b r n ∧
    !definednessTagGraph c k n ∧
    !prf p a ∧
    !prf h b ∧
    !componentsToPairGraph t p h q r n →
    !prf t c”

noncomputable def uniformProject0ToPairPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSentence :=
  ∀¹* project0ToPairPreservationMatrix w hw

noncomputable def uniformProject1ToPairPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSentence :=
  ∀¹* project1ToPairPreservationMatrix w hw

noncomputable def uniformPairToLeftPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSentence :=
  ∀¹* pairToLeftPreservationMatrix w hw

noncomputable def uniformPairToRightPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSentence :=
  ∀¹* pairToRightPreservationMatrix w hw

noncomputable def uniformComponentsToPairPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSentence :=
  ∀¹* componentsToPairPreservationMatrix w hw

theorem models_uniformProject0ToPairPreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    V↓[ℒₒᵣ] ⊧ uniformProject0ToPairPreservation w hw := by
  rw [models_iff, uniformProject0ToPairPreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v =
      ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8] := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  simp only [project0ToPairPreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons'', Matrix.comp₀,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one]
  intro h
  have hj := (project0PairIndexGraph_iff (v 4) (v 1) (v 2)).mp h.1
  have hk := (pairIndexGraph_iff (v 5) (v 1) (v 2)).mp h.2.1
  have ha := (definednessTagGraph_iff (v 6) (v 4) (v 3)).mp h.2.2.1
  have hb := (definednessTagGraph_iff (v 7) (v 5) (v 3)).mp h.2.2.2.1
  have ht := (project0ToPairGraph_iff
    (v 8) (v 0) (v 1) (v 2) (v 3)).mp h.2.2.2.2.2
  have hp : Semiformula.Evalb (M := V)
      ![v 0, definednessTagValue (project0PairIndexValue (v 1) (v 2))
        (v 3)] (productProofGraph w hw).val := by
    simpa [ha, hj] using h.2.2.2.2.1
  have hout := productProofGraph_project0ToPair w hw
    (v 0) (v 1) (v 2) (v 3) hp
  simpa [ht, hb, hk] using hout

theorem models_uniformProject1ToPairPreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    V↓[ℒₒᵣ] ⊧ uniformProject1ToPairPreservation w hw := by
  rw [models_iff, uniformProject1ToPairPreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v =
      ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8] := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  simp only [project1ToPairPreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons'', Matrix.comp₀,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one]
  intro h
  have hj := (project1PairIndexGraph_iff (v 4) (v 1) (v 2)).mp h.1
  have hk := (pairIndexGraph_iff (v 5) (v 1) (v 2)).mp h.2.1
  have ha := (definednessTagGraph_iff (v 6) (v 4) (v 3)).mp h.2.2.1
  have hb := (definednessTagGraph_iff (v 7) (v 5) (v 3)).mp h.2.2.2.1
  have ht := (project1ToPairGraph_iff
    (v 8) (v 0) (v 1) (v 2) (v 3)).mp h.2.2.2.2.2
  have hp : Semiformula.Evalb (M := V)
      ![v 0, definednessTagValue (project1PairIndexValue (v 1) (v 2))
        (v 3)] (productProofGraph w hw).val := by
    simpa [ha, hj] using h.2.2.2.2.1
  have hout := productProofGraph_project1ToPair w hw
    (v 0) (v 1) (v 2) (v 3) hp
  simpa [ht, hb, hk] using hout

theorem models_uniformPairToLeftPreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    V↓[ℒₒᵣ] ⊧ uniformPairToLeftPreservation w hw := by
  rw [models_iff, uniformPairToLeftPreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7] := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  simp only [pairToLeftPreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons'', Matrix.comp₀,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one]
  intro h
  have hk := (pairIndexGraph_iff (v 4) (v 1) (v 2)).mp h.1
  have ha := (definednessTagGraph_iff (v 5) (v 4) (v 3)).mp h.2.1
  have hb := (definednessTagGraph_iff (v 6) (v 1) (v 3)).mp h.2.2.1
  have ht := (pairToLeftGraph_iff
    (v 7) (v 0) (v 1) (v 2) (v 3)).mp h.2.2.2.2
  have hp : Semiformula.Evalb (M := V)
      ![v 0, definednessTagValue (pairIndexValue (v 1) (v 2)) (v 3)]
      (productProofGraph w hw).val := by
    simpa [ha, hk] using h.2.2.2.1
  have hout := productProofGraph_pairToLeft w hw
    (v 0) (v 1) (v 2) (v 3) hp
  simpa [ht, hb] using hout

theorem models_uniformPairToRightPreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    V↓[ℒₒᵣ] ⊧ uniformPairToRightPreservation w hw := by
  rw [models_iff, uniformPairToRightPreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7] := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  simp only [pairToRightPreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons'', Matrix.comp₀,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one]
  intro h
  have hk := (pairIndexGraph_iff (v 4) (v 1) (v 2)).mp h.1
  have ha := (definednessTagGraph_iff (v 5) (v 4) (v 3)).mp h.2.1
  have hb := (definednessTagGraph_iff (v 6) (v 2) (v 3)).mp h.2.2.1
  have ht := (pairToRightGraph_iff
    (v 7) (v 0) (v 1) (v 2) (v 3)).mp h.2.2.2.2
  have hp : Semiformula.Evalb (M := V)
      ![v 0, definednessTagValue (pairIndexValue (v 1) (v 2)) (v 3)]
      (productProofGraph w hw).val := by
    simpa [ha, hk] using h.2.2.2.1
  have hout := productProofGraph_pairToRight w hw
    (v 0) (v 1) (v 2) (v 3) hp
  simpa [ht, hb] using hout

theorem models_uniformComponentsToPairPreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    V↓[ℒₒᵣ] ⊧ uniformComponentsToPairPreservation w hw := by
  rw [models_iff, uniformComponentsToPairPreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v =
      ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  simp only [componentsToPairPreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons'', Matrix.comp₀,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one]
  intro h
  have hk := (pairIndexGraph_iff (v 5) (v 2) (v 3)).mp h.1
  have ha := (definednessTagGraph_iff (v 6) (v 2) (v 4)).mp h.2.1
  have hb := (definednessTagGraph_iff (v 7) (v 3) (v 4)).mp h.2.2.1
  have hc := (definednessTagGraph_iff (v 8) (v 5) (v 4)).mp h.2.2.2.1
  have ht := (componentsToPairGraph_iff
    (v 9) (v 0) (v 1) (v 2) (v 3) (v 4)).mp h.2.2.2.2.2.2
  have hp : Semiformula.Evalb (M := V)
      ![v 0, definednessTagValue (v 2) (v 4)]
      (productProofGraph w hw).val := by
    simpa [ha] using h.2.2.2.2.1
  have hh : Semiformula.Evalb (M := V)
      ![v 1, definednessTagValue (v 3) (v 4)]
      (productProofGraph w hw).val := by
    simpa [hb] using h.2.2.2.2.2.1
  have hout := productProofGraph_componentsToPair w hw
    (v 0) (v 1) (v 2) (v 3) (v 4) hp hh
  simpa [ht, hc, hk] using hout

theorem provable_PA_uniformProject0ToPairPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝗣𝗔 ⊢ uniformProject0ToPairPreservation w hw :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ =>
    models_uniformProject0ToPairPreservation (V := V) w hw

theorem provable_PA_uniformProject1ToPairPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝗣𝗔 ⊢ uniformProject1ToPairPreservation w hw :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ =>
    models_uniformProject1ToPairPreservation (V := V) w hw

theorem provable_PA_uniformPairToLeftPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝗣𝗔 ⊢ uniformPairToLeftPreservation w hw :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ =>
    models_uniformPairToLeftPreservation (V := V) w hw

theorem provable_PA_uniformPairToRightPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝗣𝗔 ⊢ uniformPairToRightPreservation w hw :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ =>
    models_uniformPairToRightPreservation (V := V) w hw

theorem provable_PA_uniformComponentsToPairPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝗣𝗔 ⊢ uniformComponentsToPairPreservation w hw :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ =>
    models_uniformComponentsToPairPreservation (V := V) w hw

end FailureOfComposition.NumericalProductProofs
