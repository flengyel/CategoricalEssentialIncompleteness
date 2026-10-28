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
import CategoricalEssentialIncompleteness.CategoricalTheorem
import CategoricalEssentialIncompleteness.NumericalInseparability

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
The global comparison identifies total arrows and restriction domains with
the ordinary category and its domain lattices. A natural subobject
identification along `J` then gives categorical essential incompleteness for
genuine Boolean quotients and the corresponding decision obstruction.
The proof uses the restriction, lattice, predicate, and section data;
the additional recursion and indexing structure is unused. The numerical
restriction category and PER category are constructed, with a full faithful
functor on total arrows. Restriction domains are c.e. supports; complementary
domains on ℕ are recursive sets. Actual support subobjects, their pullbacks,
and c.e. joins give the equivalence between absence of domain separators and
recursive inseparability. Numerical products, the remaining PER structure,
and the arithmetic syntax and provability comparisons remain open.
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
