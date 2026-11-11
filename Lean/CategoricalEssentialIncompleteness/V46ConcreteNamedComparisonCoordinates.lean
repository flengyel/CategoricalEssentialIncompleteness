/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonModels

/-! # Opaque projection equations for the parameterized recursion diagram -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- The operation is an arbitrary opaque arrow here. The coordinate
lemmas therefore normalize only the finite product diagram. -/
def recursionLift {P A C X : PredicateCategory T} (f : P ⨯ C ⟶ X) :
    P ⨯ (A ⨯ C) ⟶ P ⨯ (A ⨯ X) :=
  prod.lift prod.fst (prod.lift (prod.snd ≫ prod.fst)
    (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ f))

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
variable {P A C X : PredicateCategory T}

theorem recursionLift_parameter (f : P ⨯ C ⟶ X) (q : Obj T M (P ⨯ (A ⨯ C))) :
    (F T M).map (prod.fst : P ⨯ (A ⨯ X) ⟶ P) ((F T M).map (recursionLift T f) q) =
      (F T M).map (prod.fst : P ⨯ (A ⨯ C) ⟶ P) q :=
  model_lift_fst T M _ _ q

theorem recursionLift_inner (f : P ⨯ C ⟶ X) (q : Obj T M (P ⨯ (A ⨯ C))) :
    (F T M).map (prod.snd : P ⨯ (A ⨯ X) ⟶ A ⨯ X) ((F T M).map (recursionLift T f) q) =
      (F T M).map (prod.lift (prod.snd ≫ prod.fst)
        (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ f)) q :=
  model_lift_snd T M _ _ q

theorem recursionLift_head (f : P ⨯ C ⟶ X) (q : Obj T M (P ⨯ (A ⨯ C))) :
    (F T M).map (prod.fst : A ⨯ X ⟶ A)
      ((F T M).map (prod.snd : P ⨯ (A ⨯ X) ⟶ A ⨯ X) ((F T M).map (recursionLift T f) q)) =
        (F T M).map (prod.fst : A ⨯ C ⟶ A)
          ((F T M).map (prod.snd : P ⨯ (A ⨯ C) ⟶ A ⨯ C) q) := by
  calc
    _ = (F T M).map (prod.fst : A ⨯ X ⟶ A)
        ((F T M).map (prod.lift (prod.snd ≫ prod.fst)
          (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ f)) q) :=
      congrArg ((F T M).map (prod.fst : A ⨯ X ⟶ A)) (recursionLift_inner T M f q)
    _ = (F T M).map (prod.snd ≫ prod.fst : P ⨯ (A ⨯ C) ⟶ A) q :=
      model_lift_fst T M _ _ q
    _ = _ := by rw [Functor.map_comp_apply]

theorem recursionLift_result (f : P ⨯ C ⟶ X) (q : Obj T M (P ⨯ (A ⨯ C))) :
    (F T M).map (prod.snd : A ⨯ X ⟶ X)
      ((F T M).map (prod.snd : P ⨯ (A ⨯ X) ⟶ A ⨯ X) ((F T M).map (recursionLift T f) q)) =
        (F T M).map f ((F T M).map (prod.lift prod.fst
          (prod.snd ≫ prod.snd) : P ⨯ (A ⨯ C) ⟶ P ⨯ C) q) := by
  calc
    _ = (F T M).map (prod.snd : A ⨯ X ⟶ X)
        ((F T M).map (prod.lift (prod.snd ≫ prod.fst)
          (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ f)) q) :=
      congrArg ((F T M).map (prod.snd : A ⨯ X ⟶ X)) (recursionLift_inner T M f q)
    _ = (F T M).map (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ f) q :=
      model_lift_snd T M _ _ q
    _ = _ := by rw [Functor.map_comp_apply]

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
