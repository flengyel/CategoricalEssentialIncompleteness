/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalExtensionProofs.Structural.Maps

/-!
# PA-internal preservation for the finite-extension proof maps

The two preservation sentences quantify the source proof, the finite code and
program index, both endpoint formula codes, and the output proof.  Thus the
entire conversion, including endpoint construction, is expressed internally
in arithmetic.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalExtensionProofs

noncomputable section

def checkerToExtPreservationMatrix
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSemisentence 6 :=
  let prf := finiteExtensionProofGraph w hw
  “p c i a b t.
    !checkerInstanceCodeGraph a c i ∧
    !extensionInstanceCodeGraph b c i ∧
    !prf p a ∧
    !checkerToExtGraph t p c i →
    !prf t b”

def extToCheckerPreservationMatrix
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSemisentence 6 :=
  let prf := finiteExtensionProofGraph w hw
  “p c i a b t.
    !extensionInstanceCodeGraph a c i ∧
    !checkerInstanceCodeGraph b c i ∧
    !prf p a ∧
    !extToCheckerGraph t p c i →
    !prf t b”

def uniformCheckerToExtPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSentence :=
  ∀¹* checkerToExtPreservationMatrix w hw

def uniformExtToCheckerPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSentence :=
  ∀¹* extToCheckerPreservationMatrix w hw

theorem models_uniformCheckerToExtPreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    V↓[ℒₒᵣ] ⊧ uniformCheckerToExtPreservation w hw := by
  rw [models_iff, uniformCheckerToExtPreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v = ![v 0, v 1, v 2, v 3, v 4, v 5] := by
    ext j
    fin_cases j <;> rfl
  rw [hv]
  simp only [checkerToExtPreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons'', Matrix.comp₀,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one]
  intro h
  have ha := (checkerInstanceCodeGraph_iff
    (v 3) (v 1) (v 2)).mp h.1
  have hb := (extensionInstanceCodeGraph_iff
    (v 4) (v 1) (v 2)).mp h.2.1
  have ht := (checkerToExtGraph_iff
    (v 5) (v 0) (v 1) (v 2)).mp h.2.2.2
  have hp : Semiformula.Evalb (M := V)
      ![v 0, checkerInstanceCodeValue (v 1) (v 2)]
      (finiteExtensionProofGraph w hw).val := by
    simpa [ha] using h.2.2.1
  have hout := finiteExtensionProofGraph_checkerToExt
    w hw (v 0) (v 1) (v 2) hp
  simpa [ht, hb] using hout

theorem models_uniformExtToCheckerPreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    V↓[ℒₒᵣ] ⊧ uniformExtToCheckerPreservation w hw := by
  rw [models_iff, uniformExtToCheckerPreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v = ![v 0, v 1, v 2, v 3, v 4, v 5] := by
    ext j
    fin_cases j <;> rfl
  rw [hv]
  simp only [extToCheckerPreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons'', Matrix.comp₀,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one]
  intro h
  have ha := (extensionInstanceCodeGraph_iff
    (v 3) (v 1) (v 2)).mp h.1
  have hb := (checkerInstanceCodeGraph_iff
    (v 4) (v 1) (v 2)).mp h.2.1
  have ht := (extToCheckerGraph_iff
    (v 5) (v 0) (v 1) (v 2)).mp h.2.2.2
  have hp : Semiformula.Evalb (M := V)
      ![v 0, extensionInstanceCodeValue (v 1) (v 2)]
      (finiteExtensionProofGraph w hw).val := by
    simpa [ha] using h.2.2.1
  have hout := finiteExtensionProofGraph_extToChecker
    w hw (v 0) (v 1) (v 2) hp
  simpa [ht, hb] using hout

theorem provable_PA_uniformCheckerToExtPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝗣𝗔 ⊢ uniformCheckerToExtPreservation w hw :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ =>
    models_uniformCheckerToExtPreservation (V := V) w hw

theorem provable_PA_uniformExtToCheckerPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝗣𝗔 ⊢ uniformExtToCheckerPreservation w hw :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ =>
    models_uniformExtToCheckerPreservation (V := V) w hw

end

end FailureOfComposition.NumericalExtensionProofs
