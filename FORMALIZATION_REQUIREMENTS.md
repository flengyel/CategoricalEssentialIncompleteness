# Formalization requirements

The target is Definition 2.1 and the categorical essential incompleteness
theorem of *Definability and incompleteness in recursion categories*, version
16. Supporting lemmas may use weaker hypotheses. They do not by themselves
establish that the manuscript's full structures and concrete instances have
been formalized.

## What is enriched

In Kelly's terminology, the manuscript specifies a `V`-category `K`, where
`V` is the cartesian monoidal category `(V, ×, 1)`. The hom-object `H(X,Y)`
belongs to `V`; enriched composition and identities are morphisms in `V`.
The underlying ordinary category has hom-sets `V(1,H(X,Y))` and is denoted
`K₀`. This category must be a recursion category.

The domain, total-arrow, and predicate objects `E_X`, `T(X,Y)`, and `P_X`
also belong to `V`. The `P_X` are lattice objects, not categories being
enriched. The product `×` in `V` differs from the chosen restriction product
`⊗` of objects of `K₀`. For the numerical instance, `V = Set`.

Kelly's source terminology is `monoidal category` (§1.1, reprint p. 7),
`V-category`, `hom-object`, `composition law`, and `identity element` (§1.2,
p. 8), and `underlying category` (§1.3, p. 10). The introduction also uses
`base category` and `change of base-category`. Source:
[Basic Concepts of Enriched Category Theory](https://tac.mta.ca/tac/reprints/articles/10/tr10.pdf).

## Full definition and compatibility

The full interface must include the following data and proofs.

1. Hom-objects, identity, composition, restriction, restriction products, and
   zeros, with equations of morphisms in `V`, equivalently equations at every
   parameter object. Equations at global points alone are insufficient.
2. The actual equalizer defining `E_X` and pullback defining `T(X,Y)`, with
   their comparisons to restriction idempotents and total arrows of `K₀`.
   Domain meet, bottom, and top must agree with composition, zero, and identity.
3. A recursion-category structure on this same `K₀`, compatible with its
   enriched restriction, product, and zero operations. An unrelated recursion
   instance on another category does not supply this requirement.
4. The chosen Turing morphism `τ : U ⊗ U → U`, the evaluation map constructed
   from `τ`, composition, and product, and a morphism `Λ` in `V` satisfying
   `ev_τ ∘ Λ = 1`. An independently specified evaluation function is insufficient.
5. The predicate lattice objects `P_X`, total inverse images, and monic natural
   bounded-lattice maps `j_X : E_X → P_X`.
6. The total substitution arrow `s : U ⊗ U → S`, disjoint predicates `p₊,p₋`,
   and a section of the specified representation pullback. The representation
   section is additional structure; it does not follow just from `Λ`.

Existing component constructions and comparison maps should be reused.
The full-data theorem may apply the existing representation-hypothesis lemma.
No artificial use of a Turing identity, requirement that every lemma use
every field, or strengthening of the manuscript's assumptions is warranted.

## Concrete arithmetic realization

Construct the full instance from the numerical recursion category and prove
that the instantiated operations agree with the existing constructions:

- `U` and `S` are the indicated numerical coding objects.
- Substitution is the proved operation recursive jointly in formula and numeral.
- `P_X` is the full PER subobject lattice along `J`, with the actual domain
  embedding and categorical inverse images.
- The distinguished predicates are the theorem and refutation supports of
  the given theory.
- The representation section exists under the advertised strong numeralwise
  definability hypothesis; consistency is explicit. This hypothesis must not
  be replaced by a stronger Rosser or effective-inseparability hypothesis.
- Set-level choices of program or formula representatives are permitted for
  the Set instance. They must not be described as recursive selectors.

Construct the Lindenbaum PER, Boolean operations, quotient presentation,
bound-fiber identifications, and extension quotient maps before claiming that
the arithmetic result is an instance of the Boolean-presentation theorem.
The original theory need not be c.e.; enumerability is required of the
extension in the general arithmetic essential-incompleteness statement.

Theorem 8.15 of Di Paola–Heller is a possible additional intrinsic construction.
Its canonical inseparable pair is not a required intermediate of the present
manuscript proof. Any transfer from that pair to theory predicates needs a
separate proof under the stated hypotheses.

## Current interface and checks

`RepresentedQuotients.lean` exports the supporting theorem
`EnrichedRestriction.represented_boolean_quotient_incomplete` and its
bound-copairing consequence. The former `CategoricalTheorem` module and
principal-theorem names have been removed without aliases. The unrelated
root arithmetic-recursion wrapper declarations have also been removed.

The remaining representation, numerical recursion, enrichment, syntax, and
arithmetic proofs are retained. Their validity is not undermined by their
being reusable under weaker assumptions.

Compile the eventual full instance and its specialization, update the exact
axiom-audit declaration lists, and run `scripts/verify.py`. Axiom counts and
imports alone do not establish which ordinary lemmas a proof uses. Record the
construction and specialization dependencies explicitly when marking a
manuscript result complete.
