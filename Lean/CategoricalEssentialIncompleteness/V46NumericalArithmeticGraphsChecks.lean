import CategoricalEssentialIncompleteness.V46NumericalArithmeticGraphs
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.GraphsChecks

example {C D : Carrier} (f : GraphMorphism 𝗣𝗔 C D) : (liftGraph f).graph = f.graph := rfl
example {C D : Carrier} (f : GraphMorphism 𝗣𝗔 C D) (x : PredicateInterpretation.Obj ℕ C) :
    (PredicateInterpretation.functor 𝗧𝗔 ℕ).map (representedArrow 𝗧𝗔 (liftGraph f)) x =
      (PredicateInterpretation.functor 𝗣𝗔 ℕ).map (representedArrow 𝗣𝗔 f) x := liftGraph_map f x

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.GraphsChecks
