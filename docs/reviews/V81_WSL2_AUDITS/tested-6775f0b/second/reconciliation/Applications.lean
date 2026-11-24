import CategoricalEssentialIncompleteness.V46ForkTupleTuringChecks

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation
open FailureOfComposition.Kleene (eval)
open NumericalTuples (Point code)

namespace ReaderTwoNumbered

theorem both_endpoint_evaluators :
    @RecursionCategory.IsTuringMorphism TupleSpans _ tupleProducts.pcategoryStruct
      tupleProducts.pcategoryLaws endpoint endpoint endpoint (evaluatedTau .left) ∧
    @RecursionCategory.IsTuringMorphism TupleSpans _ tupleProducts.pcategoryStruct
      tupleProducts.pcategoryLaws endpoint endpoint endpoint (evaluatedTau .right) :=
  ⟨left_isTuring, right_isTuring⟩

theorem total_specialization_at_every_fork (Y : ForkSpans)
    (f : forkProduct Y universal ⟶ universal) :
    ∃ p : Y ⟶ universal, isTotal p ∧ forkProducts.map p (𝟙 universal) ≫ tau = f :=
  ⟨forkParameter f, forkParameter_total f, fork_parameterizes f⟩

theorem fibres_of_the_specialization (Y : ForkSpans) (f : forkProduct Y universal ⟶ universal)
    (j : WalkingSpan) (z : Point (Y.obj.obj j)) (x w : Point (universal.obj.obj j)) :
    Graph ((productComparison j Y universal).inv ≫ (evaluation j).map f) (pairPoint z x) w ↔
    code _ w.val ∈ eval (componentIndex f j (code _ z.val)) (code _ x.val) :=
  (component_fibre j f z x w).symm

#print axioms both_endpoint_evaluators
#print axioms total_specialization_at_every_fork
#print axioms fibres_of_the_specialization

end ReaderTwoNumbered
