/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesExtensive
public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesRegular

/-! The regular extensive structure is on the actual predicate category
and the actual total restriction splitting, for arbitrary theories extending PA. -/

@[expose] public section

noncomputable section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.PredicateInterpretation

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example : Regular (PredicateCategory T) := inferInstance

example : FinitaryExtensive (PredicateCategory T) := inferInstance

example : Regular (TotalSplit T) := inferInstance

example : FinitaryExtensive (TotalSplit T) := inferInstance

example : PredicateCategory T ⥤ (Discrete (ArithmeticModel T) ⥤ Type) := allModels T

example : (allModels T).ReflectsIsomorphisms := inferInstance

example : PreservesLimitsOfShape WalkingCospan (allModels T) := inferInstance

example : PreservesColimitsOfShape (Discrete WalkingPair) (allModels T) := inferInstance

example {C D : PredicateCategory T} (f : C ⟶ D)
    (h : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T],
      Function.Bijective ((functor T M).map f)) : IsIso f :=
  isIso_of_models_bijective T f h

example {C D : PredicateCategory T} (f : GraphMorphism T C D)
    (h : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T],
      Function.Bijective ((functor T M).map (representedArrow T f))) :
    representedArrow T f ≫ representedArrow T (converseOfModelsBijective T f h) = 𝟙 C :=
  forward_converse T f h

example {C D : PredicateCategory T} (f : GraphMorphism T C D)
    (h : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T],
      Function.Bijective ((functor T M).map (representedArrow T f))) :
    representedArrow T (converseOfModelsBijective T f h) ≫ representedArrow T f = 𝟙 D :=
  converse_forward T f h
