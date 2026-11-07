import CategoricalEssentialIncompleteness.V46NumericalArithmeticGraphsFunctor
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.GraphsFunctorChecks
example (C : PredicateCategory 𝗣𝗔) :
    theoryExtension.obj C = (C : PredicateCategory 𝗧𝗔) := rfl
example {C D : PredicateCategory 𝗣𝗔} (f : GraphMorphism 𝗣𝗔 C D) :
    theoryExtension.map (representedArrow 𝗣𝗔 f) = representedArrow 𝗧𝗔 (liftGraph f) :=
  theoryExtension_class f
example {C D : PredicateCategory 𝗣𝗔} (f : C ⟶ D)
    (x : PredicateInterpretation.Obj ℕ C) :
    (PredicateInterpretation.functor 𝗧𝗔 ℕ).map (theoryExtension.map f) x =
      (PredicateInterpretation.functor 𝗣𝗔 ℕ).map f x := theoryExtension_value f x
example {C D : PredicateCategory 𝗣𝗔} (f : C ⟶ D)
    (x : NumericalTuples.Point (numericalInterpretation.obj C)) :
    (numericalInterpretation.map f).toFun x =
      (PredicateInterpretation.functor 𝗣𝗔 ℕ).map f x := numericalInterpretation_value f x
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.GraphsFunctorChecks
