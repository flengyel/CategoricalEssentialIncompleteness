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
import CategoricalEssentialIncompleteness.LocalLifting
import CategoricalEssentialIncompleteness.DisjointJoins
import CategoricalEssentialIncompleteness.RestrictionSplitting
import CategoricalEssentialIncompleteness.RestrictionCompatibility
import CategoricalEssentialIncompleteness.PartialFunctions
import CategoricalEssentialIncompleteness.SyntacticExtension
import CategoricalEssentialIncompleteness.SyntacticFamilyExtension
import CategoricalEssentialIncompleteness.SyntacticFiniteSwitch
import CategoricalEssentialIncompleteness.ClassicalRanges
import CategoricalEssentialIncompleteness.ArithmeticCategoricalIncompleteness
import CategoricalEssentialIncompleteness.ForkObstruction
import CategoricalEssentialIncompleteness.EffectiveForkConstruction
import CategoricalEssentialIncompleteness.EffectiveForkPartialMaps
import CategoricalEssentialIncompleteness.RestrictionSpanStructure
import CategoricalEssentialIncompleteness.EffectiveForkProductFrame
import CategoricalEssentialIncompleteness.EffectiveForkCoproductFrame
import CategoricalEssentialIncompleteness.EffectiveForkWords
import CategoricalEssentialIncompleteness.WordTuples
import CategoricalEssentialIncompleteness.EffectiveForkSplitEquivalence
import CategoricalEssentialIncompleteness.EffectiveForkRangeProducts
import CategoricalEssentialIncompleteness.EnumerableChoice
import CategoricalEssentialIncompleteness.ForkSyntaxObjects
import CategoricalEssentialIncompleteness.ForkProofTreeRecursion
import CategoricalEssentialIncompleteness.ForkEssentialIncompleteness
import CategoricalEssentialIncompleteness.ForkSyntaxInitialAlgebra
import CategoricalEssentialIncompleteness.ForkObservationFunctor
import CategoricalEssentialIncompleteness.EnumerablePartialMaps
import CategoricalEssentialIncompleteness.ForkCentralNonuniversality
import CategoricalEssentialIncompleteness.EffectiveForkExtensive

import CategoricalEssentialIncompleteness.ForkCosheafExamples

import CategoricalEssentialIncompleteness.ForkNonEquivalence
import CategoricalEssentialIncompleteness.OracleMissingLift

import CategoricalEssentialIncompleteness.ArithmeticObservationFunctor
import CategoricalEssentialIncompleteness.DoublingRangeFunctor
import CategoricalEssentialIncompleteness.EffectiveForkFreeSemigroup
import CategoricalEssentialIncompleteness.StandardTrueTheory
import CategoricalEssentialIncompleteness.ForkProbeComposition
import CategoricalEssentialIncompleteness.SyntacticObservationLattice

import CategoricalEssentialIncompleteness.GeneralObservationPrinciple
import CategoricalEssentialIncompleteness.SyntacticTargetSeparators
import CategoricalEssentialIncompleteness.V46Comparison
import CategoricalEssentialIncompleteness.V46SplitCoproducts
import CategoricalEssentialIncompleteness.V46SplitSplittings
import CategoricalEssentialIncompleteness.V46SplitExtension
import CategoricalEssentialIncompleteness.V46RegularImage
import CategoricalEssentialIncompleteness.V46LogicalComparison
import CategoricalEssentialIncompleteness.V46Applications
import CategoricalEssentialIncompleteness.V46ForkComparison
import CategoricalEssentialIncompleteness.V46SyntacticComparison
import CategoricalEssentialIncompleteness.V46SyntacticExtension
import CategoricalEssentialIncompleteness.V46CategoricalLists
import CategoricalEssentialIncompleteness.V46CategoricalSyntax
import CategoricalEssentialIncompleteness.V46CategoricalListOperations
import CategoricalEssentialIncompleteness.V46CategoricalFreeVariables
import CategoricalEssentialIncompleteness.V46SyntacticSearch
import CategoricalEssentialIncompleteness.V46Inference
import CategoricalEssentialIncompleteness.V46SentenceImages
import CategoricalEssentialIncompleteness.V46FirstOrderInference
import CategoricalEssentialIncompleteness.V46Karoubi

/-!
# Logical consequence and essential incompleteness

`V46Comparison` proves the lifted-conditional comparison for arbitrary disjoint
target restriction idempotents and its complementary-conditional consequences.
`V46SplitExtension` constructs the range functor on the restriction splitting;
`V46LogicalComparison` applies the comparison to interpreted theories.
The v46 categorical syntax, inference and concrete application modules have
their exact scope recorded in `FORMALIZATION_STATUS_V46.md`.

## Local connectedness

The version 5 categorical proof is in the namespace
`CategoricalEssentialIncompleteness.LocalConnectedness`. It proves the
connected-alternative lemma, the local-switch proposition with arbitrary
partial tests, the range-functor lifting theorem, the disjoint-join sufficient
condition, and the domain incompleteness corollary. The combined theorem uses
the new source Turing diagonal to derive its inseparable pair. The restriction
splitting preserves inseparability on included objects. `PartialFunctions`
constructs the locally connected split target of arbitrary partial functions.
The syntactic model interpretation constructs a range functor and derives
inseparability of its actual Turing diagonal pair for every consistent PA
extension. Theory extension preserves this pair. The exact model family, specified finite switch,
and categorical arithmetic
application are proved. The three-point construction includes actual monic spans,
all three frames, the generated recursion category, its categorical inseparable
pair, and the equivalence of its restriction splitting with the full partial-map
category. Its syntax, finite-proof applications, cosheaf equivalence and
restriction non-equivalence are proved. Appendix C constructs the actual
oracle-domain counterexample, including its missing section and disjoint arrows
without a common upper bound. The word free-semigroup universal property,
standard-theory comparison, doubling functor and both observation constructions
are also proved. The exact scope and cited background limitation are recorded in
`FORMALIZATION_STATUS.md`.

## Earlier representation-based development

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
