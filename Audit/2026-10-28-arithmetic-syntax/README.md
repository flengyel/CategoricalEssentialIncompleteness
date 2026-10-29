# Arithmetic syntax, representation, and incompleteness: verification evidence

This checkpoint starts from `fe4c9ce037ab049bff1bdf1a383f1a6d1106567e` and
incorporates six arithmetic modules left uncommitted by the preceding session.
Four further modules construct enumerable supports, the internal section,
recursive inseparability, and the arithmetic incompleteness consequences.

- [Verification result](verification.json): 460 axiom audits, dependency pins,
  imported-source and manuscript hashes, and project-source hashes.
- [Build log](build.log): 1966 jobs, including cached dependencies.
- [Axiom inspection](axiom-audit.log) and [Lean version](lean-version.log).
- [Principal declaration types](principal-statements.log).
- [Project-source scan](source-hole-scan.json): 77 Lean files.
- [Mathematical and prose review](REVIEW.md).
- [Manuscript correspondence](../../FORMALIZATION_STATUS.md).

The proofs establish computable inverse sentence coding, joint computability
of numeral substitution, and a total numerical substitution arrow. Categorical
representation is equivalent to strong numeralwise definability, which is
also equivalent to existence of the internal representation section.
The internal categorical diagonal theorem gives recursive inseparability of
theorem and refutation supports.

`ArithmeticSyntax.essential_incompleteness_of_definability` proves that every
consistent c.e. extension of a consistent arithmetic theory strongly defining
every recursive set is incomplete. The original theory need not be c.e.
`ArithmeticSyntax.essential_undecidability_of_definability` excludes recursive
theorem support in every consistent extension. The `PA⁻` corollaries obtain
the definability hypothesis from the pinned numeralwise representation theorem.
These declarations are in the `CategoricalEssentialIncompleteness` namespace.

All 383 previous axiom checks are retained; 77 are added. No imported source,
dependency revision, toolchain pin, or manuscript file changed. The hosted
executable-path adapter was used. Palomar Comparator, NanoDa, and con-ron
were not run.

The Lindenbaum PER, its Boolean presentation and extension quotients, the
arbitrary-effective-language generalization, and the domain-predicate version
of the definability algebra remain open. The next construction is the
Lindenbaum PER and its presentation by sentence indices.
