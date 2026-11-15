/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46PredicateImageConsistency
public import CategoricalEssentialIncompleteness.V46SubobjectImagePresentations

/-! # Independent checks of image witnesses and reflected bottom subobjects -/
@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
open SyntacticPredicates

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
example {X : PredicateCategory T} (A : Subobject X)
    (h : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
      (x : M), (A : PredicateCategory T).val.Evalb ![x] → False) : A = ⊥ :=
  PredicateModelSubobjects.eq_bot_of_models_empty T A (fun M _ _ x => h M x.val x.property)

example {C D : PredicateCategory T} (f : C ⟶ D)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
    (x : PredicateInterpretation.Obj M (imageSubobject f : PredicateCategory T)) :
    ∃ c : PredicateInterpretation.Obj M C,
      (PredicateInterpretation.functor T M).map f c =
        (PredicateInterpretation.functor T M).map (imageSubobject f).arrow x :=
  PredicateModelSubobjects.imageSubobject_point T M f x

example {C X : PredicateCategory T} (f : C ⟶ X) (ν : X ⟶ X)
    (h : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
      (p q : PredicateInterpretation.Obj M C),
      (PredicateInterpretation.functor T M).map f q ≠
        (PredicateInterpretation.functor T M).map ν
          ((PredicateInterpretation.functor T M).map f p)) :
    imageSubobject f ⊓ (Subobject.pullback ν).obj (imageSubobject f) = ⊥ :=
  PredicateImageConsistency.image_consistent T f ν h

#print axioms PredicateModelSubobjects.empty_inclusion
#print axioms PredicateModelSubobjects.initialOfModelsEmpty
#print axioms PredicateModelSubobjects.eq_bot_of_models_empty
#print axioms PredicateModelSubobjects.factorThruImage_isSplitEpi
#print axioms PredicateModelSubobjects.image_point
#print axioms PredicateModelSubobjects.imageSubobject_point
#print axioms PredicateImageConsistency.image_consistent
#print axioms SubobjectImagePresentations.exists_eq_image
#print axioms SubobjectImagePresentations.exists_mk
