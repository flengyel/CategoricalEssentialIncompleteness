# Continuation: the general construction in recursion categories

Continue the mathematical construction in flengyel/CategoricalEssentialIncompleteness
on main. Use the current committed sources, not the earlier represented-Boolean-quotient
formalization. Consult Lengyel2004 together with the version-10 corrections
in flengyel/errata; read their latest committed state before importing further results.

## Current documents

- manuscript/domains_hoare_profunctors_essential_incompleteness.tex and .pdf:
  *Domains, finite proofs, and essential incompleteness*, 23 pages,
  committed at 10284d07bd46f327472ccddf1ee508d0de5c2156.
- manuscript/general_recursion_category_construction.tex and .pdf:
  *Finite proof algebras in range restriction categories*, 13 pages,
  committed at dbd8b1ad803c1436ecf6abdc1c4ef1548f7ab4c1.
- manuscript/iteration_domains_and_cosheaves.tex and .pdf:
  *Iteration domains, finite proofs, and computational cosheaves*, 14 pages.
- manuscript/range_completion_three_point_cosheaves.tex and .pdf:
  *Range completion and computational cosheaves on a three-point space*.
- manuscript/inseparable_domains_and_extensions.tex and .pdf:
  *Inseparable domains and computational extensions*, 5 pages.
- manuscript/intrinsic_introspection_and_extensions.tex and .pdf:
  *Internal theories and intrinsic incompleteness*, 3 pages: a separate
  arithmetic-universe comparison, with no established connection to the
  given recursion category or the Di Paola–Heller construction.
- Audit/2026-10-29-polynomial-proofs/, Audit/2026-10-29-general-construction/,
  Audit/2026-10-29-iteration-cosheaves/, Audit/2026-10-29-range-three-point/,
  Audit/2026-10-29-inseparable-extensions/, and
  Audit/2026-10-29-intrinsic-introspection/
  record the respective reviews,
  source checks, and verification.

The first two manuscripts remain unchanged by the cosheaf continuation.
No new theorem in these notes has been formalized in Lean. The older Lean
axiom-audit count does not verify these constructions. The latest reviews
are expressly author-side audits, not independent referee reports.

## Research target and starting data

The starting data remain a Heller recursion category R. The task is to
construct the compatible deductive presentation from that category and
prove consistency and incompleteness of every consistent computational
extension in the stated class. Domains remain restriction idempotents of
R (or of its restriction-idempotent splitting); their split objects lie
in the corresponding total category. Do not replace them by arbitrary
subobjects of a different ambient category.

The established notes give conditional construction theorems and explicit
nonnumerical recursion-category examples. Preserve those results and work
on the remaining hypotheses for appropriate general classes of recursion
categories. Simplifying unnecessary encoding choices is useful only if
the resulting construction remains attached to R and proves the required
statement about its computational theories and extensions.

The arithmetic-universe comparison note starts from different data and
proves a different result. It supplies neither a construction from R nor
a comparison of its computational domains and extensions. It discharges
none of the open construction hypotheses here. Its own extension question
must not replace this project's recursion-category target.

## Immediate mathematical work

The latest result gives a minimal construction inside the original category.
For disjoint domains a,b on U, binary restriction coproducts give the signed
presentation (U+U,swap,a+b). Its consistent computational extensions are
exactly disjoint enlargements (c,d) of (a,b), and completeness is c∨d=1.
Thus inseparability is equivalent to essential incompleteness in this class.
The construction is left adjoint to (S,ν,t)↦(S,t,ν*t) for total involutive
ν and consistent t. The adjunction needs no joins; the equivalence needs
binary domain joins but not their stability under arbitrary total pullback.
Neither result needs ranges, iteration, regularity, or a proof algebra.

The user's subsequent direction is now the primary target: construct a
category D_T intrinsically associated with each intended consistent
computational extension T and a comparison that transports its separators
back to the starting recursion category C. A direct implementation is a
restriction functor G_T:D_T→C preserving zero and binary domain joins.
With a,b inseparable on U in C, construct an assertion object Y_T and actual
theorem/refutation domains p_T,n_T in D_T. Identify G_T(Y_T) with U and
prove a≤G_T(p_T), b≤G_T(n_T). More generally, supply a total
u_T:U→G_T(Y_T) and these inequalities after u_T*, proving that this
inverse image preserves the required joins.

A separator in D_T then gives a separator in C. Consistency must imply
p_T n_T=0, and completeness must imply p_T∨n_T=1. This gives essential
incompleteness. Neither fullness nor faithfulness is required for this
backwards functor. The categories, the functor, and the domain identifications
must be constructed from the formal systems and their extension relation;
merely assuming separator reflection leaves the central task open.

The distinction is directional: for F:C→D, preservation of separators
C→D only reflects inseparability D→C. That was not the needed transfer
when C is the category with the known inseparable pair. A functor G:D→C
uses the same elementary preservation law in the useful direction.
Alternatively, a forward F:C→D may work if target separators can actually
be lifted. Do not confuse these two mechanisms.

The PA benchmark is the fixed Rosser reduction θ(n)=code(ρ(numeral n))
from a disjoint inseparable c.e. pair A,B to the theorem/refutation pair
of every consistent c.e. extension of PA. Its inverse image sends
separators backwards. An intrinsic category-level construction must recover
this connection without silently assuming soundness of the extensions.

Classical deductive closure over the signed presentation is a subsidiary
construction to test against this target. The signed presentation does not
itself supply the classical Hilbert calculus. Ordinary syntax-code negation
need not be involutive. The existing conditional proof-algebra results remain
available; no new interpretation is needed for each extension in that setting.

Indeed, its existing atom constructor θ:U→S already gives the fixed map
θ*:D(S)→D(U), with a≤θ*t₀ and b≤θ*ν*t₀ from one-node proofs.
The same inequalities hold for every t≥t₀. Every consistent extension's
theorem/refutation pair (t,ν*t) is therefore inseparable, not just incomplete.

For functors between categories, separate the two directions. A restriction
functor preserving zero and binary domain joins reflects inseparability of
a specified image pair. Full faithfulness on the relevant endomorphism set
suffices for preservation. Unrestricted preservation fails even with the
chosen evaluator preserved: the second projection from the diagonal-object
subcategory of C×C sends (a,p),(b,q) to complementary p,q, where a,b are
inseparable in C. This source is Heller-1990 prodominical, not dominical.
It does not refute the weaker claim that the target has some inseparable pair.

Any use of Ramesh's introspection must supply an actual construction
associated with R and prove its compatibility with the selected
computational domains and intended extensions. No such construction or
comparison has yet been established. Until then, the proved recursion-
category results and their remaining hypotheses below are the operative
research state.

## Established computational structure to preserve

1. Binary case distinction, a nontrivial object U, and a parameter-universal
   Turing morphism give an inseparable pair by the Turing diagonal. The
   case-distinction hypothesis is explicit.
2. Universal-object dominance and universal ranges give a total typed
   constructor embedding γ:Pq→q for W=S×U, with its range-filtered
   restriction inverse δ. Stages are e_0=0 and e_(n+1)=γP(e_n)δ.
3. The supplement's typed Turing-fold theorem constructs partial-fold
   gluing. Its evaluator is filtered by ran Δ_S before P is applied.
   Its strength identity uses only total program-parameter maps.
   Nullary constructors prevent unrestricted partial-parameter naturality.
4. The new note reconstructs Heller's iteration lemma in a split setting
   from stable length coverage of formally free semigroups. It uses only
   the semigroup functor's total action, applied to the domain and value
   maps of a partial endomorphism. The start range of the finite trace
   object is exactly the agreement union of finite termination domains.
5. A finite worklist decodes a node and replaces it by its ordered premises.
   Its singleton-input domain r_m after m steps is the finite union of
   codes of trees with at most m vertices. The constructor stage e_n is
   the finite union of codes of trees with height at most n. With
   B_0=0 and B_(n+1)=1+kB_n, e_n≤r_(B_n) and r_m≤e_m. This proves
   equality of agreement unions. It does not infer leastness from a
   fixed-point equation.
6. The note separately proves preservation of these stable unions by
   total inverse images, finite products, and finite coproducts.
   Hence it discharges both union hypotheses of the supplement for the
   stated bounded-finitary presentations. Parameters are retained.
7. Universal product-compatible ranges, splitting, weak choice, and finite
   limits of the total category imply regularity and range/image agreement.
   The proof gives the graph pullback law and kernel-pair descent.
   Heller factoriality is an alternative under the stated range/limit data.
8. For the finite-stage syntax U+X+X² and the three displayed Hilbert
   schemes plus modus ponens, consistency no longer needs decidable atom
   equality. Fix finite proof shapes and refine all formula parameters by
   syntax shape. The finitely many required equalities generate a relation
   on atom occurrences. Opposite conclusions force a positive and a
   negative axiom leaf into the same class. The branch then maps into
   A×_U B=0. Stable shape coverage proves global consistency.
9. The proof-conclusion range is the least rule-closed computational
   domain. One-node proofs give the two atomic range inequalities.
   Inseparability makes every consistent computational extension incomplete.
   No soundness of arbitrary extensions or global Boolean separator is assumed.

## Verified nonnumerical example

Let C be c.e. subsets of finite powers of N with total-on-source partial
recursive functions. The computational Sierpiński cosheaves are
E_→=C^[1], with partial maps A_→=Par(E_→,Mono).
For the opens ∅⊂V⊂X, a set-valued cosheaf is exactly an arrow C(V)→C(X);
all nonempty covers contain the covered open. Computational morphisms are
commuting recursive squares, and domains are c.e. subdiagrams.

The universal object is U=(N²→N), with transition π₂. Its evaluator at
component 1 is the ordinary universal partial recursive function.
At component 0 it runs a program returning a pair and checks that its
second output equals the component-1 computation. The compiler is a
total natural square, and the equality of represented domains is proved.
The note checks ranges, weak choice, finite limits/extensivity, stable
length coverage, dominance, frames, and binary case distinction.

The full isotypical partial subcategory generated on U's formal objects
is a recursion category; its restriction splitting is equivalent to A_→.
The total terminal object has three subobjects, not the numerical two.
The universal object lacks decidable equality because π₂ is noninjective.
Thus this example needs the equality-free consistency argument.
Its computations still use numerical component programs; do not claim
an arithmetic interpretation or a nonclassical computability theory.

## Verified three-point construction

The companion treats the space with opens ∅, {c}, {a,c}, {b,c}, {a,b,c}.
Its set-valued cosheaves are exactly covariant fork diagrams
Y_1←Y_0→Y_2, with global value the pushout Y_1 ⊔_(Y_0) Y_2.
The computational total category is C^[0→1,0→2], and partial domains
are c.e. subdiagrams. The global pushout is presented by a c.e.
equivalence relation on tagged representatives; quotient equality need
not be decidable. Every c.e. equivalence relation on N occurs this way.

The note proves finite limits, regularity, extensivity, range/image
agreement, weak choice, and stable word-length coverage on basic components.
A categorical monomorphism can induce a noninjective global pushout map.
Internal products, word objects, and syntax are consequently not obtained
by performing the corresponding set construction on every open value.

The universal object has V_0=N^4, V_1=V_2=N^2 and transitions
(k,z,a,b)↦(k,a),(k,b). The component index k supplies product, coproduct,
and nonempty-word frames. A central universal computation is accepted
only when its two endpoint computations return the required projections.
The total natural compiler proves exact parameter-universality.
The generated isotypical full partial category is a recursion category,
and its restriction splitting is the full computational fork category.

Complemented domains of V consist of whole component blocks, with a
recursive set of indices; this gives binary case distinction. V lacks
decidable equality. The total terminal object has five subobjects, unlike
the numerical two and Sierpiński three. The established finite-stage
and equality-constraint theorems therefore give essential incompleteness
in this three-point category without decidable atom equality.

## Separate range-completion target

Cockett–Guo–Hofstra I, Theorem 5.12, supplies a general algebraic range
completion. Part II, Theorem 3.27, supplies a faithful discrete cartesian
range completion R_d(C); Proposition 3.11 gives universal agreement.
The companion derives from its normal form that it adds no total arrows
on original objects. If all original objects restriction-embed in U,
preservation of the original evaluator's parameter-universality would
force the unit to be full. Thus a nonfull R_d completion requires a
different evaluator or a construction adding total program maps.

Construct a completion with explicit uniform codes for the added range
predicates and a compatible evaluator. Prove preservation or recovery
of finite coproducts, stable word-length coverage, universal dominance,
and weak choice; establish regularity using the stated hypotheses.
Do not infer these properties from the range universal property.
Use the three-point computational category as a test example.

Pointwise products of general set-valued cosheaves need not be cosheaves:
on a discrete two-point space C(V)=V gives four pairs at X but only two
in the cosheaf gluing of singleton values. The assignment of ordinary
formulas to open sets also fails descent for mixed implications.
Do not equate an internal polynomial syntax algebra with an external
assignment of recursive syntax codes without a comparison proof.

The further general problem is closure of Heller/Lengyel generated
recursion subcategories under the needed ranges and finite limits.
The ambient coalgebra results in the corrections do not by themselves
settle this. Their two-phase explicit example is numerically equivalent.

## Source and completion cautions

Inspect Heller's scan and type-check imported formulas. The equality-product
and division subscripts on p.1262 are printed incorrectly, and the final
composite of Proposition 6.2 cannot be copied as printed. The new note
reconstructs the relevant range and iteration arguments.

Heller §10, Example 5, p.1267 already constructs a generated simplicial
recursion category whose diagonal lacks a range. Attribute this prior work.
Heller's iteration definition uses stable finite-length coverage; Lengyel's
later definition assumes countable strong unions and iteration for total
endomorphisms. The version-10 corrections' §7.1 gives the graph union
argument, §11.2 states product stability explicitly, and Appendix B repairs
the range representation theorem.

The previous selected-presheaf obstruction remains valid: Garner–Lin's
representable-pullback domains do not ensure ranges. For non-c.e. B, a
selected range of F_B:∐_(n∈B)y1→yN would be the least c.e. superset of B,
and co-singleton upper bounds force equality with B. Also y0 need not be
the empty presheaf. No sheaf or cosheaf completion theorem supersedes this.

## Working requirements

State categories, variance, functor actions, map types, and universal
properties explicitly. Keep restriction idempotents in the partial category
and their split objects in the total category. Distinguish logical negation
from monotone inverse image along its constructor.

Do the mathematics before preparing updates. Use the hostile-referee and
mathematical-writing plugin instructions and keep reports outside the paper.
Preserve proved conditional statements; do not claim completion of the
Di Paola–Heller program. Reuse verification of unchanged sources, run
appropriate checks on changed sources, and report exactly which hypotheses
were discharged and which remain. No Lean rerun substitutes for a new proof.
