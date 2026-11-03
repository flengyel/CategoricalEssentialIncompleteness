import CategoricalEssentialIncompleteness.V46PredicateInterpretation

/-! Explicit all-model types for the predicate interpretation and comparison. -/

noncomputable section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory
open FailureOfComposition.ProofSearch
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.PredicateInterpretation

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

example : PredicateCategory T ⥤ Type := functor T M

example (C : PredicateCategory T) : (functor T M).obj C = {x : M // C.val.Evalb ![x]} := rfl

example {C D : PredicateCategory T} (f : GraphMorphism T C D)
    (x : Obj M C) (y : Obj M D) :
    (functor T M).map (classOfGraph T f) x = y ↔ f.graph.val.Evalb ![x.val, y.val] :=
  map_class_eq_iff T M f x y

example {C D : PredicateCategory T} (f g : GraphMorphism T C D)
    (h : Uniform T f.graph g.graph) : value T M f = value T M g :=
  value_congr T M f g h

example : TotalSplit T ⥤ Type := totalFunctor T M

example : realization T ⋙ totalFunctor T M ≅ functor T M := predicateComparison T M

example {C D : PredicateCategory T} (f : C ⟶ D) :
    (totalFunctor T M).map ((realization T).map f) ≫
        (predicateComparison T M).hom.app D =
      (predicateComparison T M).hom.app C ≫ (functor T M).map f :=
  predicateComparison_naturality T M f

example {C D : PredicateCategory T} (f g : C ⟶ D)
    (h : ∀ (N : Type) [ORingStructure N] [N↓[ℒₒᵣ] ⊧* T],
      (functor T N).map f = (functor T N).map g) : f = g :=
  jointly_faithful T f g h
