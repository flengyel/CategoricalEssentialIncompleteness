# Source checks and replacement of private citations

Baseline commit: `f1b32a4df2e677bb3dd7cfabe76720bfe0a284b5`.
Baseline source SHA-256:
`1078044059fe239c27fdc82a9b69e7995e3b28c03d7310ff1ffb4164948d439f`.

## Original near-product hypothesis

The scan of Lengyel, *More existence theorems for recursion categories*,
Annals of Pure and Applied Logic 125 (2004), printed p. 27, was inspected
directly. Section 4 defines an iteration functor by preservation of zero
morphisms, coproducts, domains, and iteration. The next paragraph expressly
says that such functors need not preserve products. Theorem 26 follows
on that page. Thus nonpreservation of the near product was permitted in
the original theorem, not introduced by the corrections.

The Introduction now attaches “without requiring preservation of the near
product” to the sentence citing both the original paper and its version-10
corrections. The awkward following sentence and its misleading restriction
to the corrected theorem are removed. The corrections citation remains
attached to the historical comparison, as the author requested.

## Private local-connectedness note

The working source `manuscript/sources/LOCOct10f.tex` contains the lifting
criterion and its proof in Proposition 4.8. No claim is made that they were
missing from that note. The preceding paper cited the result without
including it; the present paper includes its statement and proof.
The private note is absent from the paper's bibliography and citations.

| Previously cited content | Location and argument in this paper |
| --- | --- |
| Connected-domain alternative | Lemma 6.1: pull back the two summand domains and use connectedness. |
| Section of the partial injection formed from disjoint domains | Proposition 6.2: connected tests prove partial monicity, splitting handles partial tests, and weak choice supplies the unique section. |
| Range-functor inseparability with lifting | Theorem 6.3: the typed Turing factorization and target inverse-image calculation are given in full. |
| Disjoint-arrow-join sufficient condition | Proposition 6.4: upper-bound equations prove totality and the two branch equations; range agreement identifies the target image with the required section. No preservation of arrow joins is assumed. |
| Failure when the lifting hypothesis is dropped | Appendix C: the oracle-domain category is constructed, its recursion and range structure are proved, and the nonrecursive target selector has no source preimage. |

The main theorem retains the lifting hypothesis. The Introduction and
Appendix C explicitly identify the counterexample as a counterexample to
the statement with that hypothesis dropped. The separating domains in
the example belong to the oracle-domain category; their separator is not
an ordinary recursive set. The new paper does not copy the private note's
ambiguous wording “recursively separable” for that categorical conclusion.

## Three-point construction and finite proofs

The private companion `range_completion_three_point_cosheaves.tex` was a
working source, not a retained bibliographic dependency. Its needed
arguments are included in the paper. Its further private references are
not used as substitutes for proofs.

| Dependency | Internal proof |
| --- | --- |
| Cosheaves on the three-point topology | Proposition A.1 classifies the covers, constructs the global pushout, and defines the equivalence on morphisms. The c.e. quotient presentation and the distinction between basic-open and global products/subobjects are explained. |
| Finite limits, monomorphisms, regular images, and extensivity | Proposition A.2 gives numerical carriers, universal maps, descent through surjections, pullback stability, and the diagram arguments. |
| Partial maps, restrictions, ranges, weak choice, and inverse images | Proposition A.3 computes domains and values, proves the agreement and pullback laws, and constructs partial inverses of partial injections. |
| Local connectedness | Proposition A.4 proves that finite connected subdiagrams detect every component domain and value. |
| Universal object and frames | Lemmas A.5–A.6 give the embeddings, partial inverses, and explicit product, coproduct, and word isomorphisms. |
| Turing morphism | Theorem A.7 specifies the three computations, their natural c.e. domain, the compatibility tests, and the total natural parameter map; both directions of domain equality are proved. |
| Recursion category and its splitting | Proposition A.8 verifies isotypicality and the Turing property, then constructs the splitting comparison on objects and arrows and proves full faithfulness and essential surjectivity. The numerical splitting comparison is also given. |
| Nonnumericality and absence of decidable atom equality | Proposition A.9 computes five subobjects of the terminal diagram and gives the naturality obstruction to a Boolean equality test. |
| Syntax initiality | Proposition B.1 gives the covariant total polynomial and the recursive fold, its naturality, algebra equation, and uniqueness. |
| Finite proof object and theorem range | Theorem B.2 constructs the c.e. proof carriers and natural transitions, the total conclusion map, its least rule-closed image, and the two one-node proof inequalities. |
| Consistency | Theorem B.2 uses the finite positive leaves of a proposed proof/refutation pair at each component. The same finite valuation satisfies both proofs' signed leaves; the Hilbert schemes and modus ponens preserve truth. Empty intersections at all components prove the internal zero-domain equation. |

The concrete finite-tree construction suffices for the claims made here.
It does not invoke the more general private iteration/worklist or typed-fold
theorem. The consistency proof requires neither a natural family of
Boolean valuations nor a global separator of the two axiom domains.
The numerical equality used to check component proof codes does not
assert decidable equality of the diagram object.

No free range completion is used in this paper. Component images give its
ranges directly, and every restriction-splitting comparison used by the
application is explicitly proved in Appendix A. No general completion
theorem is assumed to preserve a Turing morphism.

## Other literature

The previously verified published references and the pointwise-composition
obstruction remain unchanged. Their provenance is recorded in the
[preceding source check](../2026-10-30-local-connectedness-writing/SOURCE_CHECK.md).
This revision imports no new equation from Heller's scan and does not
rely on its known typographical errors. It makes no new claim about the
priority of the classical arithmetic incompleteness theorem.
