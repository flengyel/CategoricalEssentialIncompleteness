/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PredicateInterpretationRegular

/-! Explicit generic statements for finite and regular model interpretation. -/

@[expose] public section

noncomputable section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.PredicateInterpretation

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

example : HasFiniteCoproducts (PredicateCategory T) := inferInstance

example : PreservesFiniteLimits (functor T M) := inferInstance

example : PreservesFiniteCoproducts (functor T M) := inferInstance

example (C D : Carrier) : Obj M C ⊕ Obj M D ≃ Obj M (sumCarrier C D) :=
  sumEquiv T M C D

example (C D : Carrier) : Obj M C × Obj M D ≃ Obj M (productCarrier C D) :=
  productEquiv T M C D

example (C D : PredicateCategory T) (f : C ⟶ D) :
    ∃ e : (functor T M).obj (image f) ≅ image ((functor T M).map f),
      e.hom ≫ image.ι ((functor T M).map f) = (functor T M).map (image.ι f) :=
  preserves_regularImage T M f

example (C D : PredicateCategory T) (f : GraphMorphism T C D) (y : Obj M D) :
    (imageCarrier f.graph).val.Evalb ![y.val] ↔
      y ∈ Set.range ((functor T M).map (representedArrow T f)) :=
  imageCarrier_iff_range T M f y

example : PreservesFiniteLimits (functor T M) ∧
    PreservesFiniteCoproducts (functor T M) ∧
    ∀ (C D : PredicateCategory T) (f : C ⟶ D),
      ∃ e : (functor T M).obj (image f) ≅ image ((functor T M).map f),
        e.hom ≫ image.ι ((functor T M).map f) = (functor T M).map (image.ι f) :=
  regular T M

example : PreservesFiniteLimits (totalFunctor T M) ∧
    PreservesFiniteCoproducts (totalFunctor T M) ∧
    ∀ (X Y : TotalSplit T) (f : X ⟶ Y),
      ∃ e : (totalFunctor T M).obj (image f) ≅ image ((totalFunctor T M).map f),
        e.hom ≫ image.ι ((totalFunctor T M).map f) = (totalFunctor T M).map (image.ι f) :=
  total_regular T M

example : PreservesFiniteLimits (canonicalDomainFunctor T M) ∧
    PreservesFiniteCoproducts (canonicalDomainFunctor T M) ∧
    ∀ (X Y : TotalSplit T) (f : X ⟶ Y),
      ∃ e : (canonicalDomainFunctor T M).obj (image f) ≅
          image ((canonicalDomainFunctor T M).map f),
        e.hom ≫ image.ι ((canonicalDomainFunctor T M).map f) =
          (canonicalDomainFunctor T M).map (image.ι f) :=
  canonical_regular T M
