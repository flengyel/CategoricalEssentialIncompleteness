/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalDomainOrder.Structural.Maps

/-!
# PA-internal domain-order preservation

The preservation sentence quantifies both supplied proof codes, both program
indices, the input numeral, the composite index, all three endpoint formula
codes, and the output proof code inside arithmetic.  Its proof uses the
recognized scheme leaf and two structural MP steps in every PA model.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalDomainOrder

open NumericalProductProofs

noncomputable def domainOrderTransferPreservationMatrix
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSemisentence 10 :=
  let prf := domainOrderProofGraph w hw
  “e p s r i c a b d t.
    !compIndexGraph c s r ∧
    !equalityCodeGraph a c r ∧
    !rightInstanceCodeGraph b r i i ∧
    !rightInstanceCodeGraph d s i i ∧
    !prf e a ∧
    !prf p b ∧
    !domainOrderTransferGraph t e p s r i →
    !prf t d”

noncomputable def uniformDomainOrderTransferPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    ArithmeticSentence :=
  ∀¹* domainOrderTransferPreservationMatrix w hw

theorem models_uniformDomainOrderTransferPreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    V↓[ℒₒᵣ] ⊧ uniformDomainOrderTransferPreservation w hw := by
  rw [models_iff, uniformDomainOrderTransferPreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v =
      ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] := by
    ext j
    fin_cases j <;> rfl
  rw [hv]
  simp only [domainOrderTransferPreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons'', Matrix.comp₀,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one]
  intro h
  have hc := (compIndexGraph_iff (v 5) (v 2) (v 3)).mp h.1
  have ha := (equalityCodeGraph_iff (v 6) (v 5) (v 3)).mp h.2.1
  have hb := (rightInstanceCodeGraph_iff
    (v 7) (v 3) (v 4) (v 4)).mp h.2.2.1
  have hd := (rightInstanceCodeGraph_iff
    (v 8) (v 2) (v 4) (v 4)).mp h.2.2.2.1
  have ht := (domainOrderTransferGraph_iff
    (v 9) (v 0) (v 1) (v 2) (v 3) (v 4)).mp
      h.2.2.2.2.2.2
  have he : Semiformula.Evalb (M := V)
      ![v 0, equalityCodeValue (compIndexValue (v 2) (v 3)) (v 3)]
      (domainOrderProofGraph w hw).val := by
    simpa [ha, hc] using h.2.2.2.2.1
  have hp : Semiformula.Evalb (M := V)
      ![v 1, rightInstanceCodeValue (v 3) (v 4) (v 4)]
      (domainOrderProofGraph w hw).val := by
    simpa [hb] using h.2.2.2.2.2.1
  have hout := domainOrderProofGraph_transfer w hw
    (v 0) (v 1) (v 2) (v 3) (v 4) he hp
  simpa [ht, hd] using hout

theorem provable_PA_uniformDomainOrderTransferPreservation
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝗣𝗔 ⊢ uniformDomainOrderTransferPreservation w hw :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ =>
    models_uniformDomainOrderTransferPreservation (V := V) w hw

end FailureOfComposition.NumericalDomainOrder
