import CategoricalEssentialIncompleteness.V46NumericalArithmeticUnaryImage
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.UnaryImage.Checks
variable {X : NumericalTuples.Object} {C : PredicateCategory 𝗧𝗔}
  (f : X ⟶ NumericalCoordinates.predicateObject C)
example (p : ℕ) : (object f).support p ↔ ∃ x : NumericalTuples.Point X, (f.toFun x).val = p :=
  membership f p
example : (object f).dimension = 1 := dimension f
example : quotient f ≫ inclusion f = f := factor f
example : IsImage (imageFactorisation f).toMonoFactorisation := isImage f
example [Mono f] : X ≅ object f := iso f
example [Mono f] : (iso f).inv ≫ f = inclusion f := inverse_inclusion f
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.UnaryImage.Checks
