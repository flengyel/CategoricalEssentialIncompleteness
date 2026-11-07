import CategoricalEssentialIncompleteness.V46NumericalCoordinatesValues
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalCoordinates.ValuesChecks

example {C D : PredicateCategory 𝗧𝗔} (f : C ⟶ D)
    (x : NumericalTuples.Point (predicateObject C)) :
    (predicateMap f).toFun x = (PredicateInterpretation.functor 𝗧𝗔 ℕ).map f x := predicateMap_value f x
example {C D : PredicateCategory 𝗧𝗔} (f : C ⟶ D) :
    NumericalSyntax.predicateEquivalence.functor.map f ≫ (predicatePresentationIso D).hom =
      (predicatePresentationIso C).hom ≫ predicateMap f := predicatePresentationIso_natural f
example {C D : PredicateCategory 𝗧𝗔} (f : C ⟶ D)
    (x : NumericalTuples.Point (NumericalSyntax.predicateEquivalence.functor.obj C)) :
    (predicatePresentationIso D).hom.toFun ((NumericalSyntax.predicateEquivalence.functor.map f).toFun x) =
      (PredicateInterpretation.functor 𝗧𝗔 ℕ).map f ((predicatePresentationIso C).hom.toFun x) :=
  predicatePresentationIso_natural_apply f x

end CategoricalEssentialIncompleteness.V46.NumericalCoordinates.ValuesChecks
