import PCats
import RiceShapiro
import Metamath
import Arith
import CategoricalRiceShapiro
import FailureOfComposition
import FailureOfComposition.Palomar.SolutionNine
import CategoricalEssentialIncompleteness.RestrictionPredicates
import CategoricalEssentialIncompleteness.ParameterizedEqualizer
import CategoricalEssentialIncompleteness.BooleanQuotients
import CategoricalEssentialIncompleteness.BooleanPresentations
import CategoricalEssentialIncompleteness.BooleanDecisions
import CategoricalEssentialIncompleteness.InternalRepresentation
import CategoricalEssentialIncompleteness.EnrichedQuotients
import CategoricalEssentialIncompleteness.CategoricalTheorem
import CategoricalEssentialIncompleteness.NumericalInseparability
import CategoricalEssentialIncompleteness.NumericalProducts
import CategoricalEssentialIncompleteness.PERExtensive
import CategoricalEssentialIncompleteness.NumericalPredicates

/-!
# Categorical essential incompleteness

The project proves the external diagonal theorem, the internal separator
factorization, and categorical essential incompleteness for represented Boolean
quotients. The proof constructs the restriction-domain and total-arrow objects
and compares their global points with the underlying ordinary category.

The numerical development constructs partial recursive maps, PER morphisms,
the full faithful binary-product-preserving functor on total maps, and the
comparison between domain separators and recursive separators. The PER category
is regular and finitely extensive: finite coproducts are disjoint and
satisfy the van Kampen property. The numerical domain inclusion is an injective
natural bounded lattice map into the full PER subobject predicate lattices.

The imported arithmetic declarations below check the recursion-category
instance and Turing evaluator of the typed program category. The comparison
with numerical syntax and provability is recorded in `FORMALIZATION_STATUS.md`.
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

/-- The evaluator has the categorical Turing factorization property. -/
theorem arithmeticEvaluatorIsTuring
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    IsTuringMorphism
      (PRecursionCategory.tau (C := CodedProgramCategory T)) :=
  codedProgramCategory_tau_isTuringMorphism T

end CategoricalEssentialIncompleteness
