import CategoricalEssentialIncompleteness.V46NumericalArithmeticIncompletenessDiagonal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Incompleteness.Checks
example : RecursionCategory.IsTuringMorphism
    (ClassicalPrograms.Q.map ArithmeticDiagonalCodes.sourceTau) := tauRec_isTuring
example : Inseparable (diagonal0 tauRec ClassicalPrograms.parityIso)
    (diagonal1 tauRec ClassicalPrograms.parityIso) := diagonal_inseparable
example : Inseparable (SplitObject.includedIdem aRec) (SplitObject.includedIdem bRec) :=
  included_inseparable
example : ClassicalPrograms.splitSupport (SplitObject.includedIdem aRec) =
    {n : ℕ | ArithmeticDiagonalCodes.alpha.val.Evalb ![n]} := includedA_support
example : ClassicalPrograms.splitSupport (SplitObject.includedIdem bRec) =
    {n : ℕ | ArithmeticDiagonalCodes.beta.val.Evalb ![n]} := includedB_support
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Incompleteness.Checks
