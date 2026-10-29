# Outline: Domains, finite proofs, and essential incompleteness

Florian Lengyel — 29 October 2026.

Central question: how can computational inseparability constrain effective classical deduction through explicitly typed categorical constructions?

The note proves an abstract Turing-morphism inseparability theorem under an explicit binary-case hypothesis, a witness-to-proof separation theorem, and a computational finite-proof initial-algebra theorem in the numerical restriction-idempotent splitting. Their numerical instance gives a consistent c.e. propositional theory all of whose consistent c.e. extensions are incomplete. Existence of the corresponding logical presentations in general recursion categories remains a stated problem.

## Actual outline and dependencies

1. **Computation, assertions, and deduction.** Problem, literature, and three-step argument: computational inseparability; maps from evidence to proofs; exclusion of a complete consistent extension.
2. **Restriction domains and direct images.** Restriction and range axioms; contravariant domain functor; covariant direct images; local adjunction and Frobenius. Supplies the domain calculus for later results.
3. **Hoare assertions as profunctors.** Definitions and variance; composition pseudofunctors; comparison of total and partial correctness; program order and detection of domains. Depends on §2.
4. **Weakest liberal preconditions and representability.** Presheaf representability and the global right-adjoint question. §4.1 proves the numerical iff criterion, nonuniformity, and the distinction between effective formula construction and truth decisions. Depends on §§2–3.
5. **Stable unions of domains.** Heller's agreement definition; universal ranges; preservation by meets, images, and total inverse images; the bounded-distributive-lattice-valued functor. Supplies complementary-pair pullbacks.
6. **Categorical separation and proof codes.** Complementary and inseparable domains, negation on assertion codes, consistency and completeness. The witness-square transfer theorem uses ranges and total inverse image. §6.1 proves a separate representation-based inseparability theorem used by the arithmetic corollary.
7. **The numerical category and effective unions.** Partial recursive maps on positive finite powers of the natural numbers; ranges and uniformly effective stable unions; failure for arbitrary countable families.
8. **A Turing morphism and inseparable domains.** Exact parameter-universality and binary-case hypotheses; element-free proof through the equation `dg = hg`; numerical verification of all hypotheses. Depends on the domain and binary-product calculus, not on proof syntax.
9. **Typed inference rules and polynomial functors.** Rules with premise and conclusion types; a functor on families; polynomial bicomodule structure in `(Poly, composition, identity)`; backward action on premise positions.
10. **Finite proofs in a computational category.** The total category of the numerical restriction-idempotent splitting; recursive rule presentations; polynomial slice functor and its computable finite-proof initial algebra. §10.1 defines strict translations and the proof functor. §10.2 constructs the general range functor, its natural monomorphism, and the numerical theorem-object functor.
11. **Profunctors and polynomial bicomodules.** A profunctor induces a right adjoint between covariant functor categories; its left adjoint and composition are proved. Application to the Hoare profunctors identifies Kan extension and precomposition. The distinction from a domain-valued weakest liberal precondition is explicit.
12. **A numerical deductive construction.** §12.1 constructs trace witnesses, single-atom propositional axioms, finite proofs, refutation pullback, witness-to-proof squares, consistency, and provability/refutability inseparability. §12.2 defines theories and deductive categories, represents every c.e. extension by added witnessed rules, and proves essential incompleteness. §12.3 gives the Hoare interpretation using an evaluator restricted to outputs 0 and 1. §12.4 proves the conditional arithmetic representation corollary and gives jointly recursive numeral substitution. §12.5 proves an effective interpretation criterion and compares semantic predicate transformation.
13. **Logical presentations in recursion categories.** States the remaining nonnumerical existence problem, distinguishes initial finite-proof algebras from cofree behavior trees, and identifies the additional arithmetic interpretation problem.

## Main dependency chain

- §8: Turing universality and binary cases ⇒ inseparable computational domains.
- §§9–10: recursive typed rules ⇒ computational finite-proof initial algebra ⇒ range/theorem functor.
- §12.1: finite traces ⇒ commuting positive and negative proof squares ⇒ inseparable theorem/refutation domains.
- §12.2, using §6: consistency and completeness would give a complementary separator ⇒ essential incompleteness.
- §§3–4 and 11 describe semantics and its relation to polynomial bicomodules; the incompleteness theorem does not assume representability of weakest liberal preconditions.
- §6.1 supplies the separate arithmetic conclusion in §12.4.

## Appendix dependency decision

The previous four appendices are removed. No main theorem used their closure construction, finite-hom-set obstruction, adjoining-partial-witness construction, or enrichment discussion. The increasing-finite-power clause of the stable-union lemma, used only in the closure appendix, is also removed. No appendix remains.
