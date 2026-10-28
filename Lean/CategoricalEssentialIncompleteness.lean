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
import CategoricalEssentialIncompleteness.BooleanDecisions
import CategoricalEssentialIncompleteness.InternalRepresentation
import CategoricalEssentialIncompleteness.EnrichedQuotients

/-!
# Categorical essential incompleteness: diagonal and quotient arguments

This module imports the maintained categorical Rice--Shapiro infrastructure
together with the nine proved Failure of Composition solution declarations.
It checks the concrete typed program category against the `PCats` interfaces
and imports the external diagonal argument, its restriction-idempotent
interpretation, a parameterized equalizer bridge, and the Boolean-quotient
argument, including the comparison between bound fibers and the bound
copairing. It also constructs characteristic arrows and the internal Boolean
algebra on `1 + 1`, and proves the equivalence of complete represented Boolean
extensions with represented decisions. It constructs the domain equalizers,
totality pullbacks, internal total-arrow operations, and domain inverse image
from enriched restriction hom-objects. The representation section yields the
factorization of the actual separator through the equalizer of the bounds.
It also proves the Boolean-quotient obstruction directly from that section
and an explicit subobject identification at the sentence object. The global
comparison along `J` and the numerical interpretation remain separate
obligations.
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
