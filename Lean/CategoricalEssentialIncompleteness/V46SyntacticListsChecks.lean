/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticLists

/-! # Checks for canonical list constructors and all-model product points. -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates SyntacticLists

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (V C D : PredicateCategory T)

example : ListAlgebra (D := PredicateCategory T) V := algebra T V

example : toRawProduct T C D ≫ fromRawProduct T C D = 𝟙 (C ⨯ D) :=
  toRaw_fromRaw T C D

example : fromRawProduct T C D ≫ toRawProduct T C D = 𝟙 _ :=
  fromRaw_toRaw T C D

omit [𝗣𝗔 ⪯ T] in
example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (a : M) :
    (listObject T V).val.Evalb ![a] ↔ ∀ i < len a, V.val.Evalb ![nth a i] :=
  listCarrier_eval V a

example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
    (A B : Over C) (a : Obj T M A.left) (b : Obj T M B.left)
    (h : (F T M).map A.hom a = (F T M).map B.hom b) :
    ∃ z : Obj T M (A ⨯ B).left,
      (F T M).map (prod.fst : A ⨯ B ⟶ A).left z = a ∧
      (F T M).map (prod.snd : A ⨯ B ⟶ B).left z = b :=
  modelOverProduct_exists T M A B a b h
