/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalExtensionTheta.Structural.Maps

/-!
# PA-internal preservation by the B1(8) proof maps

The two closed sentences quantify proof codes, program indices, computation
parameters, endpoint codes, and output proof codes inside arithmetic.  The
same exact theta proof graph occurs in every input and output predicate.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalExtensionTheta

open NumericalExtensionProofs

noncomputable section

def componentAndCheckerToThetaPreservationMatrix
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSemisentence 10 :=
  let prf := extensionThetaProofGraph w hw
  “p s q t c i a b h z.
    !rightInstanceCodeGraph a q t c ∧
    !checkerInstanceCodeGraph b c i ∧
    !thetaInstanceCodeGraph h q t i ∧
    !prf p a ∧
    !prf s b ∧
    !componentAndCheckerToThetaGraph z p s q t c i →
    !prf z h”

def componentAndExtToThetaPreservationMatrix
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSemisentence 10 :=
  let prf := extensionThetaProofGraph w hw
  “p s q t c i a x h z.
    !rightInstanceCodeGraph a q t c ∧
    !extensionInstanceCodeGraph x c i ∧
    !thetaInstanceCodeGraph h q t i ∧
    !prf p a ∧
    !prf s x ∧
    !componentAndExtToThetaGraph z p s q t c i →
    !prf z h”

def uniformComponentAndCheckerToThetaPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSentence :=
  ∀¹* componentAndCheckerToThetaPreservationMatrix w hw

def uniformComponentAndExtToThetaPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSentence :=
  ∀¹* componentAndExtToThetaPreservationMatrix w hw

theorem models_uniformComponentAndCheckerToThetaPreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    V↓[ℒₒᵣ] ⊧ uniformComponentAndCheckerToThetaPreservation w hw := by
  rw [models_iff, uniformComponentAndCheckerToThetaPreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v =
      ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] := by
    ext j
    fin_cases j <;> rfl
  rw [hv]
  simp only [componentAndCheckerToThetaPreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons'', Matrix.comp₀,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one]
  rintro ⟨ha, hb, hh, hp, hs, hz⟩
  have ha' := (rightInstanceCodeGraph_iff
    (v 6) (v 2) (v 3) (v 4)).mp ha
  have hb' := (checkerInstanceCodeGraph_iff
    (v 7) (v 4) (v 5)).mp hb
  have hh' := (thetaInstanceCodeGraph_iff
    (v 8) (v 2) (v 3) (v 5)).mp hh
  have hz' := (componentAndCheckerToThetaGraph_iff
    (v 9) (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)).mp hz
  have hp' : Semiformula.Evalb (M := V)
      ![v 0, rightInstanceCodeValue (v 2) (v 3) (v 4)]
      (extensionThetaProofGraph w hw).val := by
    simpa [ha'] using hp
  have hs' : Semiformula.Evalb (M := V)
      ![v 1, checkerInstanceCodeValue (v 4) (v 5)]
      (extensionThetaProofGraph w hw).val := by
    simpa [hb'] using hs
  have hout := extensionThetaProofGraph_componentAndCheckerToTheta
    w hw (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) hp' hs'
  simpa [hz', hh'] using hout

theorem models_uniformComponentAndExtToThetaPreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    V↓[ℒₒᵣ] ⊧ uniformComponentAndExtToThetaPreservation w hw := by
  rw [models_iff, uniformComponentAndExtToThetaPreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v =
      ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] := by
    ext j
    fin_cases j <;> rfl
  rw [hv]
  simp only [componentAndExtToThetaPreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons'', Matrix.comp₀,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one]
  rintro ⟨ha, hx, hh, hp, hs, hz⟩
  have ha' := (rightInstanceCodeGraph_iff
    (v 6) (v 2) (v 3) (v 4)).mp ha
  have hx' := (extensionInstanceCodeGraph_iff
    (v 7) (v 4) (v 5)).mp hx
  have hh' := (thetaInstanceCodeGraph_iff
    (v 8) (v 2) (v 3) (v 5)).mp hh
  have hz' := (componentAndExtToThetaGraph_iff
    (v 9) (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)).mp hz
  have hp' : Semiformula.Evalb (M := V)
      ![v 0, rightInstanceCodeValue (v 2) (v 3) (v 4)]
      (extensionThetaProofGraph w hw).val := by
    simpa [ha'] using hp
  have hs' : Semiformula.Evalb (M := V)
      ![v 1, extensionInstanceCodeValue (v 4) (v 5)]
      (extensionThetaProofGraph w hw).val := by
    simpa [hx'] using hs
  have hout := extensionThetaProofGraph_componentAndExtToTheta
    w hw (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) hp' hs'
  simpa [hz', hh'] using hout

theorem provable_PA_uniformComponentAndCheckerToThetaPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝗣𝗔 ⊢ uniformComponentAndCheckerToThetaPreservation w hw :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ =>
    models_uniformComponentAndCheckerToThetaPreservation (V := V) w hw

theorem provable_PA_uniformComponentAndExtToThetaPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝗣𝗔 ⊢ uniformComponentAndExtToThetaPreservation w hw :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ =>
    models_uniformComponentAndExtToThetaPreservation (V := V) w hw

end

end FailureOfComposition.NumericalExtensionTheta
