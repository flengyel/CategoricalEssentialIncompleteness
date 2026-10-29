# Numerical recursion category: source review

This review covers `NumericalEnumeration`, `NumericalIsotype`,
`NumericalTuring`, and `NumericalRecursion`. All four modules were read in
full, together with the numerical source restrictions, total-arrow
construction, product action, and recursion-category interfaces used in
their proofs. The manuscript comparison concerns
`sec:integration-numerical` and the indexing requirement preceding
`def:generalized-definability-algebra`. The preceding checkpoint is
`06f4e14ea2ce77bc57afd0f72068026a95466c69`.

## A. Correctness findings

No concrete defect was found in the four modules. They construct recursive
isomorphisms between every numerical object and the natural numbers, prove
the full Turing factorization property, and supply the numerical
`PRecursionCategory` instance. A chosen program code also gives an ordinary
indexing function with its evaluation equation. The Set-enriched numerical
realization and arithmetic interpretation remain to be constructed.

## B. Constructions and hypotheses

`NumericalEnumeration` proves computability of the number of elements of
a recursive predicate below a given bound by recursion on the bound.
Its increasing enumeration is computed by searching for an element whose
preceding count is the prescribed index. Infinitude supplies such an
element at every index, so the partial recursive search is total. The
`Nat.nth` and `Nat.count` equations prove both inverse identities on their
respective domains. Computability is proved for the enumeration and the
counting function separately.

`NumericalIsotype` turns these functions into total numerical arrows using
`totalFromFunction`. The enumeration arrow has all natural numbers as its
domain; the counting arrow has exactly the numerical source carrier as
its domain. The two composite identities are proved as equalities of
partial functions on all natural-number inputs. In particular, the
composite on a numerical object is undefined outside its carrier, as is
its categorical identity. The constructions give `natIso` in `Numerical`,
`totalNatIso` in `Numerical.Total`, and `objectIso X Y` for every pair of
objects. Thus the isotype instance follows from recursive isomorphisms.

`NumericalTuring` defines the evaluator on a recursive pair of a program
code and an argument. Its partial recursiveness follows from
`Code.eval_part` and the computable decoding and unpairing functions.
For a program `c`, the parameter arrow sends an input `n` in the source
carrier to the code of `Code.curry c n`. This arrow is total on its source,
and the membership lemma records that it is undefined outside that source.

The theorem `turingEvaluator_parameterization` assumes a code whose
evaluation equals the given partial function and proves
`partialProdMap (codeParameter V c).hom (𝟙 nat) ≫ turingEvaluator = φ`.
The proof compares membership of every possible output at every natural
input. Its forward implication uses `Code.eval_curry`; its reverse
implication obtains source membership from `φ.source` before constructing
the paired intermediate value. Consequently the equality includes the
domains of definition and inputs outside the product carrier. The theorem
`turingEvaluator_isTuringMorphism` quantifies over every numerical parameter
object `V` and every partial arrow `φ : product V nat ⟶ nat`.

`NumericalRecursion` combines the preceding prodominical structure,
isotype instance, and evaluator into the imported recursion-category
interface, taking all three distinguished objects to be `nat`.
The function `turingIndexing V` chooses a code whose evaluation is the
given extensional partial arrow and returns its total parameter arrow.
The choice specification and the factorization theorem prove its
evaluation equation. Each resulting parameter arrow is recursive; the
definition is an ordinary function on sets of arrows.

## C. Local issues

The recorded full verification passed: the build completed with 1,949 jobs,
and all 336 axiom audits passed, retaining the preceding 311 declarations.
The audited dependencies are confined to `propext`, `Classical.choice`,
and `Quot.sound`. The verification record contains hashes for 61 integration
files, including the verifier. The source scan covers 60 project Lean files
and reports no proof omissions or new unproved declarations. The two
pre-existing imported linter warnings remain. These conclusions were
checked against the recorded logs and JSON reports; this source review
did not itself run Lean or the verifier.

The module order follows the mathematical dependencies: computable
enumeration, categorical isomorphisms, the Turing morphism, and the
recursion-category instance. The supplied copy of Knuth, Larrabee, and
Roberts's *Mathematical Writing*, Section 1, was consulted for the prose
review. The comments introduce the constructions and use established
terminology. No terminology defect requiring a source change was found.
This review makes no whole-manuscript editorial judgment.

## D. Consistency and dependency check

Objects remain infinite recursive subsets of the natural numbers, and
arrows remain extensional partial recursive functions with domain contained
in the source carrier. Infinitude is used to make the enumeration total;
recursiveness is used for both counting and search. Neither property is
replaced by the existence of an arbitrary set bijection.

`Numerical.Total` records totality for the original numerical restriction,
whereas `IsTuringMorphism` uses the restriction induced by the P-category.
The proof of `turingEvaluator_isTuringMorphism` converts the totality
condition explicitly using `pcategory_rst_eq`. The previously proved
`inducedRestriction_eq` identifies the two restriction structures.
The new modules introduce no instance-priority changes.

The choice of program code is justified by `Code.exists_code` for the
actual partial function underlying each arrow. No effective operation
selecting a code from an extensional function is assumed. To obtain the
manuscript's internal indexing arrow, the ordinary function at `V = nat`
must still be transported through the Set-enriched hom and total-arrow
comparisons. Its evaluation equation is distinct from the representation
section involving theorem and refutation predicates.

No new unproved axiom or hypothesis restating a desired conclusion occurs
in the four modules. Their declarations preserve the existing numerical
domain lattice, PER predicate lattice, and natural embedding. The
recursion-category instance does not identify the numerical category with
the imported typed arithmetic program category. No imported source,
dependency pin, or manuscript file changed in this checkpoint.

## E. Remaining requirements

The next construction is `H : InternalHom (Type) Numerical`, using the
existing hom-sets, identities, composition, products, projections, and
partial pairing. Pointwise restriction must supply
`R : EnrichedRestriction H`, together with `R.Products` and `R.Zeros`.
The first substantive lattice comparison identifies the
equalizer `R.domainObject X` with `Numerical.Domain X`. Transporting the
existing lattice pointwise to every parameter type then supplies
`R.DomainLattices`, including precomposition and preservation of joins by
partial inverse image. The predicate lattices and natural embedding must
likewise be internalized, and the global category and total-arrow functor
must be compared with the existing numerical constructions. A comparison
only at global points does not provide all these parameterized equations.

The remaining arithmetic dependencies are:

1. Effective sentence and unary-formula coding, the recursive sentence
   bijection, and the joint recursive numeral-substitution map `s(a,n)`;
   theorem and refutation supports and their disjointness under consistency.
2. `prop:integration-arbitrary-adequacy`, identifying the two representation
   equations with strong numeralwise definability, followed by the actual
   representation section of `cor:numerical-definability-algebras`.
3. The Lindenbaum PER Boolean algebra, its presentation by a regular
   epimorphism, and the identification of its bound fibers with the two
   supports.
4. The theory-extension quotient correspondence, the equivalence between
   represented bound fibers and c.e. axiomatizability, and the comparison
   of categorical completeness with completeness of theories. The
   Boolean-homomorphism interpretation also requires the correspondence
   with complete decidable consistent extensions and the effective
   completion of decidable theories.
5. The PA representation instance and its preservation under extension,
   giving `cor:arithmetic-representation-incompleteness` through the
   preceding categorical and numerical comparisons.

For the last step, the pinned Foundation file
`Foundation/FirstOrder/Arithmetic/R0/Representation.lean` already supplies
`codeOfComputablePred_provable` and
`codeOfComputablePred_provable_neg`. They give positive numeral-instance
proofs under extension of `R₀` and negative numeral-instance proofs under
extension of `PA⁻`, respectively, without a soundness hypothesis. These
results provide the required arithmetic representation implications once
the syntax and numerical comparisons are constructed.
`Arith.FixedFormulaNumeralSubstitution` establishes recursiveness with the
formula fixed; the joint map varying the formula code also needs a proof.
Numeralwise provability of individual instances remains distinct from
provability of one universally quantified sentence.

## F. Scope and assessment

The reviewed constructions establish the manuscript's numerical recursion
category and an ordinary indexing function. The categorical
essential-incompleteness theorem is already proved from the stated
restriction, predicate, lattice, and representation-section data. Its
proof does not use the additional recursion or indexing structure.
The numerical subobject lemma and the separator/inseparability comparison
are established. Parts (i) and (iii) of
`thm:integration-essential-equivalence`,
`prop:numerical-boolean-extensions`, and the arithmetic corollary remain
open.

No confirmed or suspected mathematical defect was identified in the four
reviewed modules. The unresolved arithmetic comparisons are the principal
remaining requirement for the full intended application. This review did
not assess the other manuscript claims, novelty, or new literature
references. Palomar Comparator, NanoDa, and con-ron were not run.
