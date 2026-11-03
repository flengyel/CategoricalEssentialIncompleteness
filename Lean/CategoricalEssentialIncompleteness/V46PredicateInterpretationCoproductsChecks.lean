import CategoricalEssentialIncompleteness.V46PredicateInterpretationCoproducts

/-! Explicit source coproducts and their all-model interpretation. -/

noncomputable section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.PredicateInterpretation

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

example : IsInitial (C := PredicateCategory T) emptyCarrier := emptyIsInitial T

example (C D : PredicateCategory T) :
    IsColimit (BinaryCofan.mk (representedArrow T (sumInl T C D))
      (representedArrow T (sumInr T C D))) :=
  sumIsColimit T C D

example : HasFiniteCoproducts (PredicateCategory T) := inferInstance

example : PreservesFiniteCoproducts (functor T M) := inferInstance

example (C D : Carrier) : Obj M C ⊕ Obj M D ≃ Obj M (sumCarrier C D) :=
  sumEquiv T M C D
