import PCats
import RiceShapiro
import Metamath
import Arith
import CategoricalRiceShapiro
import FailureOfComposition
import FailureOfComposition.Palomar.SolutionNine
import CategoricalEssentialIncompleteness.RestrictionPredicates
import CategoricalEssentialIncompleteness.InternalBridge
import CategoricalEssentialIncompleteness.BooleanQuotients
import CategoricalEssentialIncompleteness.BooleanPresentations

/-!
# Categorical essential incompleteness: diagonal and quotient arguments

This module imports the maintained categorical Rice--Shapiro infrastructure
together with the nine proved Failure of Composition solution declarations.
It checks the concrete typed program category against the `PCats` interfaces
and imports the external diagonal argument, its restriction-idempotent
interpretation, a parameterized equalizer bridge, and the Boolean-quotient
argument, including the comparison between bound fibers and the bound
copairing. The full enriched and numerical comparisons remain separate obligations.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RecursionCategory
open FailureOfComposition.TypedProgramCategory
open FailureOfComposition.TypedRecursionCategory

namespace CategoricalEssentialIncompleteness

/-- The arithmetic model uses the existing categorical recursion interface. -/
noncomputable abbrev arithmeticRecursionCategory
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    PRecursionCategory (CodedProgramCategory T) := inferInstance

/-- The packaged evaluator has the categorical Turing factorization property. -/
theorem arithmeticEvaluatorIsTuring
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    IsTuringMorphism
      (PRecursionCategory.tau (C := CodedProgramCategory T)) :=
  codedProgramCategory_tau_isTuringMorphism T

end CategoricalEssentialIncompleteness
