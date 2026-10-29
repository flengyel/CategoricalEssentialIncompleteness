# Source check: range completions and three-point cosheaves

Date: 29 October 2026.

The repository baseline is 896163707ed3eaa61a30f1d881e8a9f18a3ec0c8.
The three preceding mathematical sources are reused without modification.
Their Heller scan and Lengyel2004/version-10 errata checks remain in
[the preceding source record](../2026-10-29-iteration-cosheaves/SOURCE_CHECK.md).

## Cockett–Guo–Hofstra

Primary publications:

- [Range categories I: General theory](https://www.tac.mta.ca/tac/volumes/26/17/26-17abs.html),
  Theory and Applications of Categories 26(17) (2012), 412–452.
- [Range categories II: Towards regularity](https://www.tac.mta.ca/tac/volumes/26/18/26-18abs.html),
  Theory and Applications of Categories 26(18) (2012), 453–500.

The official PDF endpoint failed during this session. The author-uploaded
full texts were consulted through [Part I](https://www.researchgate.net/publication/265194097_Range_categories_I_General_theory)
and [Part II](https://www.researchgate.net/publication/265186383_RANGE_CATEGORIES_II_TOWARDS_REGULARITY).
The focused range-completion checker also inspected the Part II PDF at
printed pp.483–484 to resolve bars lost by text extraction.

| Location | Verified use |
| --- | --- |
| I §4.11, p.439 | Universal agreement is additional axiom RR.5, not one of the four basic range axioms |
| I §5.3 and Theorem 5.12, p.451 | Free range construction, unchanged objects, tree presentation, and left adjoint |
| II Proposition 3.11, p.476 | In cartesian range categories, discreteness is equivalent to RR.5 |
| II §3.4, pp.479–481 | Discrete ranges do not by themselves imply regularity; regularization is a separate fractions construction |
| II Construction 3.21 and Lemma 3.22, pp.483–484 | An arrow has a representative [k,h] with h=fk, normalized so the restrictions of k and h agree |
| II Theorem 3.27, pp.489–490 | Faithful product-preserving unit and universal extension formula F'(q)=F(f) ran F(k) |

The new note derives, rather than attributes as a separately named theorem,
that every arrow of this discrete completion lies below an original arrow,
and hence that it adds no total arrows on its unchanged objects.
The proof explicitly addresses uniqueness up to isomorphism: the lifted
identity transformation has identity components because the unit is
identity on objects. The subsequent evaluator obstruction is proved directly.

The fractions proof of Theorem 3.19 was not reconstructed here, and no
construction step relies on its omitted detailed fraction verifications.
The note does not claim that a range completion preserves a Turing morphism,
weak choice, coproducts, or length coverage merely by its universal property.

## Cosheaf definition and prior mathematics

Justin Curry, [Sheaves, Cosheaves and Applications](https://arxiv.org/abs/1303.3255),
2014, §§2.1–2.2, fixes the covariant coequalizer definition. Its primary PDF
was checked in the preceding continuation. The three-point equivalence,
computational quotient presentation, internal operations, dominance,
frames, and filtered evaluator are proved in the present note.

The finite-stage theorem and equality-free consistency theorem are cited
at the exact preceding repository version, Corollary 4.2 and Theorem 5.3.
The supplement's type filter and total-parameter strength condition are
retained. No theorem is imported from the older Lean axiom audit.

This is a targeted source check, not an exhaustive priority search.
Heller's prior range-failure example and the selected-presheaf obstruction
remain attributed in the unchanged preceding documents.
