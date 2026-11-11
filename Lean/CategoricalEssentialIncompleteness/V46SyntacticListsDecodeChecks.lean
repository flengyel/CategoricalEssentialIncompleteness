/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticListsDecode

/-! # Checks for the actual arbitrary-family algebra decoder. -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates SyntacticLists

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (P V : PredicateCategory T)
variable (B : ListAlgebra (D := Over P) (constantFamily P V))

example : SyntacticListEvaluation.SliceAlgebra T P V B.carrier.left := decode T B

example : nilMap T B ≫ B.carrier.hom = 𝟙 P := nilMap_over T B

example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
    (p : Obj T M P) (v : Obj T M V) (x : Obj T M B.carrier.left)
    (h : (F T M).map B.carrier.hom x = p) :
    ∃! y : Obj T M B.carrier.left,
      (decodedCons T B).val.Evalb ![p.val, v.val, x.val, y.val] :=
  decodedCons_existsUnique T B M p v x h
