# Source and formalization-scope review

The development proves a representation-hypothesis inseparability lemma,
its represented-Boolean-quotient consequence, and an arithmetic essential
incompleteness consequence. The numerical recursion category and indexing
equations are also proved. The full compatible definability-algebra instance
and arithmetic specialization of the Boolean-presentation theorem remain
unfinished.

A supporting theorem's use of fewer hypotheses does not invalidate it or
disqualify the manuscript's program. The arithmetic consequence follows
through the categorical inseparability theorem, without applying an imported
arithmetic incompleteness theorem.

## Source comparison

Di Paola and Heller, *Dominical categories: recursion theory without elements*,
Journal of Symbolic Logic 52(3) (1987), 594–635, was consulted in the supplied
PDF. Reviewed passages include pages 594–596, Proposition 7.7 on pages
617–618, and Definition 8.14 and Theorem 8.15 on pages 625–626. The last two
pages were also checked visually.

Theorem 8.15 constructs recursively inseparable domains from a Turing
morphism. The proof obtains a total tagged decision morphism from a supposed
complemented separator, uses the Turing property to index it, and derives a
contradiction by self-application. Diagonalization occurs inside the proof
of inseparability.

The paper defers the proposed application to algebraic formal systems to
subsequent work. Its canonical pair is one possible construction, not a
mandatory intermediate for every categorical generalized-incompleteness
theorem. No automatic transfer into arbitrary theory predicates is asserted.

## Interface correction

The former `CategoricalTheorem.lean` module is now `RepresentedQuotients.lean`.
Its supporting declaration is
`EnrichedRestriction.represented_boolean_quotient_incomplete`; the
bound-copairing consequence is renamed correspondingly. Their unused
product-preservation arguments are removed. No deprecated aliases or
replacement principal-theorem stubs are supplied.

The disconnected root aliases `arithmeticRecursionCategory` and
`arithmeticEvaluatorIsTuring` are removed. Their imported source constructions
are retained. The actual numerical recursion, enrichment, representation,
effective syntax, and arithmetic proofs are retained.

The complete project build and `scripts/verify.py` passed with 458 axiom
audits, the previous 460 minus the two removed aliases. Both audit lists
were updated for the renamed declarations. Dependency pins and manuscript
source/PDF hashes are unchanged. A subsequent one-line module-comment edit
replaced the old module name; it changes no declaration or proof.

## Completion requirements

[FORMALIZATION_REQUIREMENTS.md](../../FORMALIZATION_REQUIREMENTS.md) specifies
the full definition, compatibility obligations, numerical instance, and
arithmetic Lindenbaum construction. The full theorem may legitimately use a
proved lemma on its restriction/predicate/representation data. It must not
substitute an unrelated recursion-category instance for the manuscript's
underlying category or describe Set-level choices as recursive selectors.

This review supersedes the earlier inference that an unused Turing hypothesis
by itself establishes failure of the mathematical program. It is a focused
source and dependency review, not a certification of the entire manuscript.
