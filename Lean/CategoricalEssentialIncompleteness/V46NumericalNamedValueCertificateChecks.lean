import CategoricalEssentialIncompleteness.V46NumericalNamedValueCertificate

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalNamedValueCertificateChecks
open NumericalNamed
variable {C D : PredicateCategory 𝗧𝗔} {X Y : NumericalTuples.Object}
variable (f : C ⟶ D) (g : X ⟶ Y)
variable (i : X ≅ NumericalCoordinates.predicateObject C)
variable (j : Y ≅ NumericalCoordinates.predicateObject D)

example (h : g ≫ j.hom = i.hom ≫ NumericalCoordinates.predicateMap f)
    (out : PredicateInterpretation.Obj ℕ C → ℕ)
    (hs : ∀ a, ((PredicateInterpretation.functor 𝗧𝗔 ℕ).map f a).val = out a)
    (x : NumericalTuples.Point X) :
    (j.hom.toFun (g.toFun x)).val = out (i.hom.toFun x) :=
  predicate_operation_value f g i j h Subtype.val out hs x

end CategoricalEssentialIncompleteness.V46.NumericalNamedValueCertificateChecks
