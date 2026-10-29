# Arithmetic syntax and representation: source review

The reviewed source starts from `fe4c9ce037ab049bff1bdf1a383f1a6d1106567e`.
The scope is the new arithmetic modules and their correspondence with the
arithmetic-language instance of the manuscript's strong numeralwise
definability subsection. This is an author-side source audit, not independent
peer review or a whole-manuscript review.

## (A) Kill-shots / hard blockers

No mathematical defect was found in `ArithmeticSyntax`,
`ArithmeticFormulaSubstitution`, `ArithmeticNumericalSubstitution`,
`ArithmeticRepresentation`, `ArithmeticSupports`, `ArithmeticAdequacy`, or
`ArithmeticEnumerableSupports`. The subsequent review also read
`ArithmeticRepresentationSection`, `ArithmeticInseparability`, and
`ArithmeticEssentialIncompleteness`, together with their immediate internal
section and separator interfaces; no defect was found there.

`ArithmeticSyntax.sentenceEquiv` distinguishes two roles for natural numbers.
Unary-formula inputs are canonical syntax codes; outputs of
`substitutionFunction` are indices in the sentence enumeration. The inverse
equations for `sentenceEnumeration` and `sentenceIndex`, together with
`sentenceEnumeration_substitutionFunction`, prove their relationship.
Noncanonical unary-formula codes denote falsity. The substitution function
remains total on all pairs of natural numbers.

`computable_numeralSubstitutionCode` uses the arithmetized substitution function
over the fixed standard natural numbers. Its encoding equation and decoding
prove computability jointly in the formula and the numeral. The standard-model
arithmetic instances used here impose no extra axioms on the theory `T` in
the later representation results.

## (B) Major weaknesses

No source-level blocker was found in the reviewed scope.

`ArithmeticSyntax.representsPair_iff` compares categorical pullbacks of PER
support inclusions with provability and refutability at every parameter and
numeral. `exists_representsPair_iff_strongNumeralwise` evaluates a representing
parameter arrow at zero in one direction and uses a constant formula-code
arrow in the other. Consistency is used to turn the two implications in a
strong numeralwise definition into equivalences.

`every_pair_represented` specializes this result to consistent extensions of
`PA⁻`. The general equivalence has no arithmetic-strength, c.e., or soundness
hypothesis. `StrongNumeralwise.mono` proves preservation under deductive
extension. The quantifier over numerals remains external to provability.

`theoremSupport_enumerable` and `refutationSupport_enumerable` require only
`T.RE`, meaning that the axiom set is c.e. Foundation's Craig axiomatization
is primitive recursive and mutually derivable with `T`; its arithmetized
provability predicate gives the two c.e. supports. The proof does not assume
consistency or soundness. The support identities and predicate equalities
identify their partial identities with numerical restriction domains.

`representationSectionOfPairs` uses the existing pullback constructor
`sectionOfRepresentative` after proving its defining equation.
`representationSection_iff_definability` proves both directions under
consistency alone. The choice of representatives is a map of sets, as required
by the `Type` enrichment; the proof does not assert a recursive selection from
domain indices.

`no_separator_of_representationSection` applies the categorical theorem
`enriched_no_global_separator` with the proved numerical nontriviality
condition. The support comparison then gives recursive inseparability.
In a complete consistent c.e. theory, the theorem and refutation supports are
complementary c.e. sets, so the theorem support is recursive. A recursive
theorem support of any consistent extension would separate the original
theorem and refutation supports. This establishes the general essential
incompleteness and undecidability conclusions without invoking an imported
incompleteness theorem.

## (C) Minor issues

The supplied copy of Knuth, Larrabee, and Roberts's *Mathematical Writing*,
Section 1, was consulted. Points 5, 11, 14, and 26 were applied to theorem
hypotheses, introduced variables, consistent notation, and unnecessary jargon.
The review follows the source order: syntax coding; joint substitution;
numerical arrows; numeralwise representation; theorem/refutation predicates;
the representation equivalence; enumerable supports.

| Source anchor | Finding | Repair |
| --- | --- | --- |
| `ArithmeticSyntax.validSentenceCodes` and enumeration comments | “Actual codes” does not identify the relevant encoding condition. | Use “canonical codes.” |
| `ArithmeticFormulaSubstitution` comments | “Actual formula encoding” adds no mathematical distinction. | Use “formula encoding.” |
| `ArithmeticSupports.theoremPredicate`, `refutationPredicate` | “Genuine” is an unsupported assurance about a defined subobject. | Delete the adjective. |
| `ArithmeticAdequacy.pull_support_eq_snd_iff` and module introduction | The same redundant assurance accompanies the pullback comparison. | Delete it and retain the proved equality. |
| `ArithmeticRepresentation` module introduction | A denial of universal closure repeats the explicit definition. | Retain the individual-instance definition and remove the denial. |

These repairs concern prose only. Definition order and code-versus-index
distinctions were retained. The table's diagnoses are applications to these
sources, not quotations or additional rules attributed to the book.

## (D) Cross-section consistency failures

No inconsistency was found between the reviewed declarations and the
arithmetic instance of `prop:integration-arbitrary-adequacy`.
The manuscript allows an arbitrary effective classical language; these
modules use Foundation's arithmetic language and arithmetic numeral terms.
The declaration correspondence must retain that scope.

The general essential-incompleteness statement retains precisely the
consistency and definability hypotheses on the original theory. It quantifies
over every deductive extension whose axioms are c.e. and which is consistent.
The original theory need not be c.e. `PA⁻` is used only in the specialized
corollaries that obtain the definability premise from representation.

## (E) Acceptance conditions, non-negotiable

The integrated entry point builds in 1966 jobs and all 460 transitive axiom
audits pass, retaining every previous declaration. The source and dependency
hash checks cover the final source state. The accompanying verification
record documents these checks. No completion claim for the Lindenbaum
presentation or its theory-extension correspondence follows from the
representation equivalence alone.

## (F) Not checked / uncertainty log

The manuscript PDF and its unmodified sections were not reviewed anew.
No novelty assessment or external literature review was performed.
Palomar Comparator, NanoDa, and con-ron were not run.

Strongest confirmed blocker: none in the reviewed scope. Strongest suspected
unconfirmed blocker: none identified. The remaining material mathematical
comparison is the Lindenbaum Boolean presentation and its theory-extension
correspondence. Recommendation on the complete manuscript formalization:
unknown until those constructions are supplied; the local source review found
no required mathematical repair.
