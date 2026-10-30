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
- manuscript/local_connectedness_and_essential_incompleteness.tex and .pdf:
  *Local connectedness, range functors, and essential incompleteness*,
  30 October 2026.
  It constructs a faithful range functor from S_T to a locally connected
  product of partial-function categories and proves the required lifting.
  It also constructs effective endpoint functors from the split three-point
  computational cosheaf category and proves that every consistent selected
  extension has recursively inseparable observed theorem/refutation sets.
  Its introduction includes the relevant literature from LOCOct10f, and
  partial-map and restriction definitions precede the constructions.
  Lengyel2004 is cited together with the version-10 corrections. The invalid
  pointwise systems S'_T of Di Paola–Montagna are excluded by Lengyel's
  composition-failure paper; the uniform quotients S_T are retained.
- manuscript/sources/LOCOct10f.tex: unchanged supplied source,
  SHA-256 039000cafbe3636ae501125d403e8fe15d42effe1c37580346d108a5bec32aab.
  The necessary switching and lifting proofs are included in the new note.
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
- Audit/2026-10-29-separator-transfer/ reviews the valid unprimed S_T
  construction, the actual theory-extension quotients, and effective
  observations of identity and zero. It records the PA benchmark and
  candidate data for its nonnumerical generalization; it is not a new
  mathematical manuscript.
- Audit/2026-10-30-syntactic-models/ records the model-family construction,
  source checks, hostile and writing reviews, and PDF verification.
- Audit/2026-10-30-local-connectedness-writing/ records the current renamed
  manuscript's introduction, literature review, definition order, and
  verification. Earlier audit reports retain their original filenames and
  hashes as historical records.

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

The latest result supplies a concrete range functor for the S_T route.
For consistent T⊇PA, let Mod_ω(T) be all arithmetic structures on carrier
N satisfying T; their operations need not be standard. Interpret each
standard program's arithmetic graph in each model. The resulting covariant
F_T:S_T→D_T, D_T=∏_{M∈Mod_ω(T)}Pfn, is faithful by completeness and
countable Löwenheim–Skolem. It preserves restrictions, ranges, zeros,
restriction products, coproducts, and finite domain joins. D_T is split,
locally connected, and satisfies weak choice and stable domain joins.
S_T itself is NOT locally connected for consistent c.e. T: retain
Di Paola–Montagna Corollary 4.4 and never transfer the target property
back to the source merely because F_T is faithful.

For complementary source domains, one program dovetails their Σ₁ witness
searches and returns the appropriate tagged input. T proves its universal
halting and exact graph from the uniform complement equations. Its
interpretation is the required section in every coordinate simultaneously.
Thus all hypotheses of LOCOct10f's range-functor lifting theorem are
discharged for S_T. For T⊆T', restricting the model family gives
π_(T,T'):D_T→D_T' and π_(T,T')F_T=F_T'Q_(T,T'). No soundness is used.
The target need not be a recursion category; Turing universality is used
in S_T. Every target domain is complemented, so arbitrary target
separators do not lift. The semantic functor is not an effective functor
to the classical recursion category.

For c.e. T, E_T(c)={n:T proves C(numeral n)} remains the effective
observation. It is also characterized by F_T(c)F_T(κ_n)=F_T(κ_n), where
κ_n is the total constant program. Proof and refutation of the fixed
machine-output predicate give disjoint c.e. enlargements of a classical
inseparable pair. Completeness would give a recursive separator. This
effective step is separate from semantic faithfulness.

The three-point alternative also satisfies the local-connectedness
theorem: use the full inclusion of its isotypical recursion category into
its split computational partial-map category. Finite subdiagrams generated
by central elements and their endpoint images, and endpoint singletons,
are connected and detect all partial maps. Fullness supplies the switch
lifts. Do not require the isotypical source itself to be split.

The three-point effective observation is now constructed. Let A be its split
computational partial-map category and K the restriction splitting of the
classical recursion category. For either endpoint i=1,2, component evaluation
E_i:A→K is an actual covariant functor on partial arrows preserving
restrictions, zeros, ranges, binary products and coproducts, and finite
domain joins. It preserves the chosen Turing morphism. The analogous central
evaluation preserves the listed structure but not that Turing morphism's
universality. The endpoint functors also have an intrinsic description:
total maps H_i→Y from the singleton endpoint diagram are the observations,
and partial postcomposition is defined exactly when the composite is total.

Fix the already constructed classical presentation with syntax S, atom map
theta:V→S, negation constructor nu:S→S, and selected theorem domain t_0.
For a consistent computational extension t≥t_0, put theta_i=E_i(theta) and
P_(i,t)=theta_i^(-1)(E_i(t)),
N_(i,t)=theta_i^(-1)(E_i(nu^*t)), identifying numerical domains with their
c.e. carriers. These are disjoint c.e. subsets of N² containing the fixed
recursively inseparable carriers A_i,B_i of E_i(a),E_i(b).
Every such observed pair is therefore recursively inseparable; completeness
would make the two sets cover N² and yield a recursive separator. The
assignment t↦(N²,P_(i,t),N_(i,t)), with identity maps for extension inclusions,
is a covariant functor to Pair(Rec).

Next, identify a class of effective atomic observation functors beyond this
fixed source and construct compatible comparison maps when computational
presentations change. Preserve the specified inseparable pair and the atomic
proof inclusions, and check the required inverse-image and domain-join laws.
A full functor from arbitrary S_T to classical Rec remains unconstructed and
is not supplied by F_T or by the separate three-point endpoint functors.
In new mathematical text, call the inseparability proof the Turing-morphism
argument; reserve “diagonal” for the categorical map Δ_U.

The preceding result gives a minimal construction inside the original category.
For disjoint domains a,b on U, binary restriction coproducts give the signed
presentation (U+U,swap,a+b). Its consistent computational extensions are
exactly disjoint enlargements (c,d) of (a,b), and completeness is c∨d=1.
Thus inseparability is equivalent to essential incompleteness in this class.
The construction is left adjoint to (S,ν,t)↦(S,t,ν*t) for total involutive
ν and consistent t. The adjunction needs no joins; the equivalence needs
binary domain joins but not their stability under arbitrary total pullback.
Neither result needs ranges, iteration, regularity, or a proof algebra.

The user's subsequent direction is the primary target: transport separators
back to a fixed recursion category with an inseparable pair. Start the PA
benchmark from the established unprimed categories S_T, not a new quotient
construction. Their arrows are program indices modulo one uniform T-proof
of equality; the invalid pointwise quotients S'_T are excluded.

For T⊆T', the actual functor is Q_(T,T'):S_T→S_T', identical on objects
and sending [e]_T to [e]_T'. It preserves the chosen Turing morphism,
its total parameter maps, and the fixed computational operations. The
latest review proves a simpler comparison through the effective presentations:
I_T={e:[e]_T=1} and Z_T={e:[e]_T=0} are disjoint c.e. subsets of the
program-index object in the fixed classical category Rec. A fixed total
recursive index map r sends the canonical output-0/output-1 diagonal pair into
I_PA,Z_PA. Thus that pair is recursively inseparable. Q preserves identity
and zero, giving I_T⊆I_T' and Z_T⊆Z_T'. Consistency keeps these enlarged
pairs disjoint. Completeness would decide I_T by parallel proof search for
the uniform identity equation or its negation, producing a separator.
It does not imply I_T∪Z_T=N.

This is an actual covariant functor from the poset of consistent c.e.
extensions into Pair(Rec), with identity maps on program indices for theory
inclusions. Separators pull back along those maps and the fixed index map r.
The map from program indices to S_T(omega,omega) is a set-presentation map,
not a functor from the extensional category Rec. The alternative observation
E_T([D])={n:T proves D(numeral n)} is a well-defined monotone map on domain
posets; it need not preserve binary joins and is not extended to all arrows.

The theorem should apply to theories admitting compatible computational
presentations. Existence of such a presentation is sufficient; constructing
it from every recursion category is not a prerequisite. The subsequent
OTHER_THEORIES.md review establishes actual further instances. For an
effective interpretation theta of PA in T, take the inverse-image theory
T^theta={phi:T proves phi^theta}. It is a consistent c.e. extension of PA,
so the already-valid category S_(T,theta)=S_(T^theta) applies. Extensions
and compatible interpretations give the same covariant quotient functors.
Checked cases include ACA_0, Kaye--Wong's specified finite set theory,
and HA through the Goedel--Gentzen negative translation. These instances
use arithmetic translations; no intrinsically nonnumerical interpretation
is claimed for them.

Precompleteness is a relevant established categorical hypothesis. Bernardi
(1986) defines it for equivalence-relation domains and proves an
inseparability theorem under c-plus-dominical hypotheses. Attribute that
prior work; do not silently apply it to nondominical S_T. The uniform
program-equivalence relation of PA is precomplete, and enlargement preserves
precompleteness. The numerical class argument applies also to c.e. lambda
theories: the classes of the two Church Booleans are inseparable, and no
consistent c.e. lambda theory is maximal consistent. This latter application
uses the fixed classical recursion category; it does not construct a new
Heller category out of each lambda theory.

Further work can test appropriate existing theory presentations against
these structural hypotheses and check weaker arithmetic bases. The three-point
computational cosheaf category now supplies a nonnumerical realization with
actual endpoint functors on partial arrows. Further classes and changes of
presentation remain to be treated. No new range completion is needed for the
established applications; a full backwards arrow functor from arbitrary S_T
has not been constructed.

A restriction functor G_T:D_T→C preserving zero and binary domain joins
is a sufficient implementation, realized by the endpoint functors for the
three-point construction and still to be constructed for further classes.
For theorem/refutation domains p_T,n_T on Y_T, supply a total
u_T:U→G_T(Y_T) with a≤u_T*G_T(p_T), b≤u_T*G_T(n_T), and prove the
needed inverse-image join law. Consistency must give p_T n_T=0 and
completeness p_T∨n_T=1. Neither fullness nor faithfulness is required.
Merely assuming these data leaves their construction open.

The distinction is directional: for F:C→D, preservation of separators
C→D only reflects inseparability D→C. That was not the needed transfer
when C is the category with the known inseparable pair. A functor G:D→C
uses the same elementary preservation law in the useful direction.
Alternatively, a forward F:C→D may work if target separators can actually
be lifted. Do not confuse these two mechanisms.

For the canonical machine-output pair, finite computation verification and
PA-provable output disjointness already give a fixed reduction to the
theorem/refutation pair of every consistent c.e. extension. A separate
Rosser comparison formula is unnecessary for this particular pair. The
earlier Rosser reduction remains applicable to general disjoint c.e. pairs.
Neither argument assumes soundness of the extensions.

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
chosen Turing morphism preserved: the second projection from the diagonal-object
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
   gluing. The typed partial map obtained from its Turing morphism is
   filtered by ran Δ_S before P is applied.
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

The universal object is U=(N²→N), with transition π₂. Its Turing morphism at
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
The total natural parameter map proves exact parameter-universality.
The generated isotypical full partial category is a recursion category,
and its restriction splitting is the full computational fork category.

Complemented domains of V consist of whole component blocks, with a
recursive set of indices; this gives binary case distinction. V lacks
decidable equality. The total terminal object has five subobjects, unlike
the numerical two and Sierpiński three. The established finite-stage
and equality-constraint theorems therefore give essential incompleteness
in this three-point category without decidable atom equality.

The current range-functor note constructs the endpoint observations and their
extension functor to Pair(Rec), as specified under Immediate mathematical
work above. Thus the next step concerns further source categories and
compatible changes of presentation, rather than constructing observations
for this example.

## Separate range-completion target

Cockett–Guo–Hofstra I, Theorem 5.12, supplies a general algebraic range
completion. Part II, Theorem 3.27, supplies a faithful discrete cartesian
range completion R_d(C); Proposition 3.11 gives universal agreement.
The companion derives from its normal form that it adds no total arrows
on original objects. If all original objects restriction-embed in U,
preservation of the original Turing morphism's parameter-universality would
force the unit to be full. Thus a nonfull R_d completion requires a
different Turing morphism or a construction adding total program maps.

Construct a completion with explicit uniform codes for the added range
predicates and a compatible Turing morphism. Prove preservation or recovery
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
