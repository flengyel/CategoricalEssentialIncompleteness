# Continuation: iteration domains and computational cosheaves

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
- Audit/2026-10-29-polynomial-proofs/, Audit/2026-10-29-general-construction/,
  and Audit/2026-10-29-iteration-cosheaves/ record the respective reviews,
  source checks, and verification.

The first two manuscripts remain unchanged by the cosheaf continuation.
No new theorem in these notes has been formalized in Lean. The older Lean
axiom-audit count does not verify these constructions. The latest reviews
are expressly author-side audits, not independent referee reports.

## Established structure to preserve

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

## Next mathematical target

Try a cosheaf construction with a genuinely nontrivial covering condition.
The proposed test space has opens
∅, {c}, {a,c}, {b,c}, {a,b,c}. Its two proper maximal opens cover X.
A cosheaf realizes the pushout of the extension maps from C({c}).

Determine a precise computational category for these diagrams, then:

- Construct the required pushouts. Identify whether their quotient equality
  remains computable, or whether different carriers are needed.
- Prove finite limits, actual categorical products, extensivity, and
  agreement of selected ranges with regular images in that category.
- Construct a universal object, compatible frames, and a typed
  parameter-universal evaluator with exact computational domains.
- Verify stable word-length coverage and closure under the trace/worklist
  construction. Apply the existing equality-free consistency theorem only
  after these hypotheses have been established.

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
