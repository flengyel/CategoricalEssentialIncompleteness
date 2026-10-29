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
import CategoricalEssentialIncompleteness.RepresentedQuotients
import CategoricalEssentialIncompleteness.NumericalInseparability
import CategoricalEssentialIncompleteness.NumericalProducts
import CategoricalEssentialIncompleteness.PERExtensive
import CategoricalEssentialIncompleteness.NumericalPredicates
import CategoricalEssentialIncompleteness.NumericalComplementedSubobjects
import CategoricalEssentialIncompleteness.NumericalTotalComparison
import CategoricalEssentialIncompleteness.NumericalDomainComparison
import CategoricalEssentialIncompleteness.NumericalRecursion
import CategoricalEssentialIncompleteness.NumericalEnrichedSubobjects
import CategoricalEssentialIncompleteness.ArithmeticAdequacy
import CategoricalEssentialIncompleteness.ArithmeticEnumerableSupports
import CategoricalEssentialIncompleteness.ArithmeticEssentialIncompleteness

/-!
# Restriction predicates, represented quotients, and arithmetic incompleteness

The project proves the external diagonal theorem, the internal separator
factorization, and incompleteness of represented Boolean quotients under
representation-section hypotheses. The proof constructs the restriction-domain
and total-arrow objects and compares their global points with the underlying
ordinary category. The intrinsic connection from Turing computation to the
predicates of a theory is not established by this quotient theorem.

The numerical development constructs partial recursive maps, PER morphisms,
the full faithful binary-product-preserving functor on total maps, and the
comparison between domain separators and recursive separators. The PER category
is regular and finitely extensive: finite coproducts are disjoint and
satisfy the van Kampen property. The numerical domain inclusion is an injective
natural bounded lattice map into the full PER subobject predicate lattices.
The complemented subobjects of the equality PER on `ℕ` are exactly recursive
support inclusions, equivalently the upper fibers of Boolean arrows.
Numerical restriction products give a prodominical P-category with the
original restriction operation. Its total-arrow category and domain lattices
are compared with the existing numerical presentations, including products,
bounded lattice operations, and restriction inverse image.
Computable enumeration and counting give recursive isomorphisms between
numerical objects. Universal program evaluation gives a Turing morphism and
a recursion-category instance. Choosing program codes gives a set-level
indexing function satisfying the evaluation equation.
The numerical Set-enrichment constructs the domain equalizers, totality
pullbacks, and their pointwise comparisons at every parameter type.
Its internal indexing morphism is a section of evaluation. Full PER subobjects
give internal predicates and a monic natural domain embedding. The global
partial and total categories are equivalent to their numerical counterparts,
and the global predicates are naturally identified with PER subobjects along
the product-preserving numerical functor.

Arithmetic sentence coding and numeral substitution define a total numerical
substitution arrow, computable jointly in the formula code and numeral.
The internal representation projection has a section exactly when every
recursive set is strongly definable numeralwise in the theory. The internal
diagonal theorem then gives recursive inseparability of theorem and refutation
indices. Every consistent c.e. extension of such a theory is incomplete.
These results specialize to consistent extensions of `PA⁻`.

The numerical recursion-category and indexing constructions are separate from
the representation-based inseparability argument. These results do not yet
realize the arithmetic theorem as a Lindenbaum instance of the represented
Boolean quotient theorem.
-/
