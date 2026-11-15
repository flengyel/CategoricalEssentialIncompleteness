/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PredicateModelSubobjects
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonParameterPoints

/-! # Consistency of categorical images from all-model proof exclusion -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.PredicateImageConsistency
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- The image consistency equation follows from exclusion of two source
witnesses in every arithmetic model. -/
theorem image_consistent {D X : PredicateCategory T} (c : D ⟶ X) (ν : X ⟶ X)
    (exclude : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
      (p q : PredicateInterpretation.Obj M D),
      (PredicateInterpretation.functor T M).map c q ≠
        (PredicateInterpretation.functor T M).map ν
          ((PredicateInterpretation.functor T M).map c p)) :
    imageSubobject c ⊓ (Subobject.pullback ν).obj (imageSubobject c) = ⊥ := by
  let A := imageSubobject c
  let B := (Subobject.pullback ν).obj A
  let I := A ⊓ B
  apply PredicateModelSubobjects.eq_bot_of_models_empty T I
  intro M _ _ z
  let l : (I : PredicateCategory T) ⟶ A := Subobject.ofLE I A inf_le_left
  let r : (I : PredicateCategory T) ⟶ A :=
    Subobject.ofLE I B inf_le_right ≫ Subobject.pullbackπ ν A
  obtain ⟨p, hp⟩ := PredicateModelSubobjects.imageSubobject_point T M c
    ((PredicateInterpretation.functor T M).map l z)
  obtain ⟨q, hq⟩ := PredicateModelSubobjects.imageSubobject_point T M c
    ((PredicateInterpretation.functor T M).map r z)
  have hr : r ≫ A.arrow = (l ≫ A.arrow) ≫ ν := by
    dsimp only [r, l]
    rw [Category.assoc, (Subobject.isPullback ν A).w, ← Category.assoc,
      Subobject.ofLE_arrow, Subobject.ofLE_arrow]
  have he := ConcreteNamedComparison.parameterPoint_diagram T M
    r A.arrow (l ≫ A.arrow) ν (by simpa only [Category.assoc] using hr) z
  have hl : (PredicateInterpretation.functor T M).map (l ≫ A.arrow) z =
      (PredicateInterpretation.functor T M).map c p := by
    rw [Functor.map_comp_apply]
    exact hp.symm
  exact exclude M p q (hq.trans (he.trans
    (congrArg ((PredicateInterpretation.functor T M).map ν) hl)))

end CategoricalEssentialIncompleteness.V46.PredicateImageConsistency
