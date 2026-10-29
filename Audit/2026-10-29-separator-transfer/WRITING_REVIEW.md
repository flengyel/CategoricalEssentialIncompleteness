# Mathematical-writing review

Date: 29 October 2026. Reviewed documents:
`CONSTRUCTION_REVIEW.md` and `SYNTACTIC_SOURCE_CHECK.md` in this directory.
This is an author-side editorial review of research audit records, not a
publication manuscript. Their source-scope statements, comparison with
earlier discussions, and account of remaining work therefore belong in
the documents.

The central argument is readable and its categorical roles are distinct:
the valid unprimed categories `S_T` provide computational equations;
extensions give quotient functors; proof enumeration supplies external
computational observation domains. The new identity/zero argument gives
the result directly from two fibers of the program presentation map and
a fixed compiler. The report correctly separates these set and domain
maps from a functor on all arrows. Its important distinction between
external consistency and internal consistency is explicit.

**Provisional source status.** The governing source required by the
mathematical-writing plugin is Knuth, Larrabee, and Roberts,
*Mathematical Writing*. The official Stanford report and bibliographic
page could not be retrieved in this session; the report request returned
a timeout. No supplied copy was available for this review. Accordingly,
this is a provisional editorial review. The recommendations below have
explicit editorial or typing reasons and are not attributed to
unverified quotations, numbered rules, or page locations in that book.

## Current outline

| Location | Function |
| --- | --- |
| Construction review, opening | States the identity/zero observation result before the comparison's scope. |
| §1 | Defines the uniform provability quotient `S_T`, its domains, and the quotient functors induced by theory inclusion; identifies the distinguished diagonal pair. |
| §2 | Defines the identity and zero fibers `I_T,Z_T`, proves their inseparability using the compiler `r`, and constructs the extension functor `I` into `Pair(Rec)`. |
| §3 | Defines and types the effective observation map `E_T`; gives its limited preservation laws and equation-only description. |
| §4 | Gives the domain-observation version of the same obstruction and the covariant extension functor `O`. |
| §5 | Separates the computational presentation, effective positive and negative proof observations, computation verification, and logical connection into candidate axiomatic data. |
| §6 | Distinguishes the valid quotient, internal and external totality, internal and external consistency, and the role of effectiveness. |
| §7 | Compares the earlier constructions by their actual role in this benchmark. |
| Source scope | Records sources checked and earlier results reused. |
| Source check, primary files and definitions | Records source provenance and the valid unprimed definitions. |
| Source check, reconstructed calculations | Verifies the congruence, domain operations, case operation, extension quotients, and preservation of the specified diagonal pair. |
| Source check, extraction and consistency distinction | Records the observation map and the exact external/internal boundary needed by the application. |

The order follows the proof dependencies. No replacement outline is
needed. The revised opening now states the positive finding before
listing scope exclusions.

## Findings and recommended repairs

| Anchor | Issue | Rationale | Repair |
| --- | --- | --- | --- |
| Construction review, opening | The finding is delayed behind scope statements. | A research review is easier to use when its result is stated first. | Lead with the valid `S_T` construction, proof observations of computational equations, and the fixed compiler that supplies the separator reduction. |
| Both documents, categorical operation | Some passages use “evaluator” for the categorical universal computation operation. | The user's explicit correction requires stable terminology; the intended structural datum is a Turing morphism. | Use “Turing morphism” for the categorical operation, keeping machine-level output relations and trace predicates separately named. |
| Source check, “Fix a primitive recursive evaluator graph” | The phrase conflates a primitive recursive computation-trace predicate with the generally nonrecursive graph of a universal partial recursive function. | These objects have different definability properties. | Specify a primitive recursive computation-trace predicate and its existentially defined Sigma_1 output relation `G_e(x,y)`, with functionality provable in PA. |
| Construction review, target `Pair(Rec)` (now §2) | Objects and arrows of this target category were used without a local definition. | The functor's morphism action should be checkable from the stated target. | Define objects `(X,A,B)` with disjoint c.e. domains and total recursive arrows `f` satisfying `A⊆f⁻¹C`, `B⊆f⁻¹D`; identity and composition are inherited from `Rec`. |
| Construction review, proof instances (now §§2,4) | The prose switched between `alpha(bar n)` and `alpha(n)` for a closed arithmetic sentence. | Distinguish an external natural number from the numeral substituted into an arithmetic formula. | Keep the numeral bars in internal provability assertions or declare the abbreviation explicitly. |
| Construction review, §2, diagonal pair | The numbering `phi_n` should be named before its first displayed use. | The compiler and the canonical pair depend on the chosen program numbering. | Introduce the PA-formalized numbering used by the chosen Turing morphism. |
| Construction review, §5, item 2 | “Arithmetic equations” can suggest atomic arithmetic equalities, whereas `Eq(e,i)` is a quantified graph-equivalence sentence. | Separate a categorical equation from the arithmetic sentence representing it. | Say “a uniform family of arithmetic sentences expressing computational equations.” |
| Source check, primary files inspected | The construction review stated that FailureOfComposition v37 had been checked, but its inspected artifact was initially omitted from the source list. | The scope assertion needs a reproducible source location. | Add the pinned repository revision, file link, and the introduction and equation-label anchors supporting the unprimed/pointwise distinction. |

All eight repairs were implemented and checked. The v37 source record
now gives repository revision `506d1f1494d6c05b0ba304edf5fe0bfa6c32864b`,
the source-file link, the introductory exclusion of unprimed `S_T`, and
the equation labels `eq:uniform` and `eq:pointwise`. No unresolved
editorial correction remains from the table. The report should retain the distinction between
arbitrary inseparable-pair preservation and preservation of the particular
canonical pair by a separate argument in every target. It should also
retain the fact that completeness makes the external separator search
total, without claiming that its totality is provable in `T`.

## Definitions, variance, and logical distinctions

- `S_T` uses one uniform proof with the universal quantifiers inside
  provability. Composition is defined on program representatives and
  the source check supplies the required congruence calculation.
- The domain order is provable implication, not inclusion of standard
  extensions. The domain operations and restriction totality are given
  before the quotient functor is used.
- The added range paragraph types `f:X -> Y`, defines the Sigma_1
  image predicate on `Y`, and derives its least-domain property in the
  uniform provability order. The use of the representing partial
  identity in the equation `R_f f=f` is explicit. It identifies the
  unchanged range program after theory extension. The final addition
  separately proves agreement: the maps `g,h:Y -> Z` are typed, the
  input witness and functionality of `f` are named, and the graph
  equivalence is explicitly derived under `R_f(y)` before concluding
  `gR_f=hR_f` uniformly in `T`. Thus leastness and agreement are stated
  as distinct properties with their respective arguments.
- `Q_{T,T'}` has explicitly specified objects, arrows, covariance,
  identity, and composition laws. The claim about the canonical pair is
  more restricted than preservation of every inseparable pair.
- The Turing morphism now has an explicit type and parameter property,
  with a restriction-total program-parameter map supplied by the
  PA-formalized s-m-n theorem. This is stronger and more precise than an
  untyped reference to code interpretation.
- `q_T` is explicitly a map of sets. Its fibers `I_T,Z_T` are c.e.
  index domains, while its values are endomorphism classes in `S_T`.
  The equality `q_T'=Q q_T` correctly relates this presentation map to
  the actual category quotient.
- The compiler `r` is total and primitive recursive. Its PA-verified
  graph specification explains each of the two reduction inclusions.
  The report does not strengthen those inclusions to inverse-image
  equalities.
- Completeness in the identity/zero argument decides `I_T` by proof
  search for its defining sentence or its negation. It is explicitly
  not used to assert that every program is provably identity or zero.
- Both extension functors `I` and `O` have the same explicitly defined
  source and target categories. Their arrow actions are identity
  programs, justified by monotonicity of the relevant proof domains.
- `E_T` is a covariant monotone map between fixed domain posets, regarded
  as thin categories. It is not presented as inverse image along an
  arrow, nor as a functor on the whole syntactic category.
- Well-definedness of `E_T` uses uniform provable equivalence; its
  effective presentation uses proof enumeration. The extension law is
  an inequality, with its correct direction.
- Finite-meet and bound preservation are separated from binary-join
  preservation. The proof of incompleteness does not assume the latter.
- The equation `e kappa_n=kappa_n` is typed without a terminal object.
  The statement defines an observation of an existing arrow class; it
  does not redefine arrow equality by numeralwise proofs.
- `A,B`, the extracted positive domains, and the theorem/refutation
  domains `C_T,N_T` are distinct pairs. The proof uses the appropriate
  inclusions and does not silently identify them.
- Logical negation in `N_T` is negation of an arithmetic sentence.
  The report does not assume that this predicate defines a complemented
  domain internally in `S_T`.
- The candidate observation axioms distinguish monotonicity of positive
  observations in a domain from antitonicity of negative observations.
  Both kinds of observation are monotone in theory extension. These
  different variances are no longer conflated.
- Consistency supplies disjoint external proof domains. Completeness
  supplies their external coverage. Neither is substituted for an
  internal proof of consistency or an internal proof of totality.
- The table of earlier constructions preserves their conditional
  mathematical results while explaining why they are unnecessary for
  this numerical benchmark. The nonnumerical construction task remains
  explicitly stated.

## Scope

Both complete revised Markdown documents were read, including the new
identity/zero proof and expanded Turing-morphism specification. No PDF was requested,
created, compiled, or rendered. This review does not independently
verify the scanned primary sources or certify the mathematical
reconstruction; the source record and focused mathematical audit state
those checks. It makes no novelty claim and does not convert the
classical benchmark into a construction for arbitrary recursion
categories.

The final inspected documents have these SHA-256 hashes:

- `CONSTRUCTION_REVIEW.md`: `7cbdf5422f0881e06e41b830a83212d706820abaa18d38deb9b7729cf07d0e03`.
- `SYNTACTIC_SOURCE_CHECK.md`: `72c4dde93a0ab9f262839b7463fb598e714f7fda09094815504400aa018dc6d7`.
