# Positive supports and finite atom valuations for Lemma 8.9

Seven producers and two independent Checks modules construct the positive-leaf
assignment and finite atom valuations for signed arithmetic derivations.
Lemma 8.9 remains open: the formula valuation and its internal truth invariant,
consistency of the generated sentence image and essential-incompleteness
assembly remain to be proved. The current count is **70 of 77 numbered results
proved, with seven open**. Theorem 5.3 remains complete.

## Mathematical construction

Work in the predicate category of PA. Let A and B be the positive and negative
axiom-label predicates. The canonical
first-order nullary rule labels form L coproduct (A coproduct B), where L is
the logical-label object. Write R for this rule presentation and Der(R) for
its constructed proof object. `SignedDerivation.positiveLeafAssignment` is a
morphism from L coproduct (A coproduct B) to List(A). It assigns
the empty list to a logical or negative leaf and the singleton list to a
positive leaf. `positiveSupport` instantiates the incoming
`DerivationFiniteSupport.collect` to give a morphism Der(R) to List(A) on the
original proof algebra and the constructed stable list algebra for A.
Its nullary, unary and binary
constructor equations are proved. The interpreted output belongs to List(A),
so every entry satisfies A in every PA model, including at nonstandard
internal lengths. `canonical_negative_lookup` derives value zero for each
B-label on the concatenation of the two collected supports, using disjointness.

The chosen categorical coproducts and literal numerical tagged sums are
compared by `sumIso` and `axiomIso`. `RuleRelabelling` constructs translations
in both directions with the identity formula morphism. Folds from the actual
initial derivation algebras prove equality of both formula-conclusion and
sentence-conclusion images. Thus the literal numerical rule presentation
generates the canonical theory. Both initiality proofs are constructed by
`SyntacticDerivation.derivationInitial`. The general generation API continues
to use initial algebras for axiom subobjects and first takes the regular image
of an arbitrary axiom morphism.

For a literal derivation word p, `positiveLabels p` retains precisely its
positive axiom labels, with repetitions. Its membership characterization,
append equation and positive-predicate bound hold for arbitrary internal
words in every PA model. The filter inspects numerical constructor tags and
equality; it does not decide membership in A or B. Its actual standard
function is proved primitive recursive.

For two successful literal derivation codes p and q, the common list is
`jointLabels p q = append (positiveLabels p) (positiveLabels q)`. The atom
assignment sends n to the existing recursive `member n (jointLabels p q)`.
PA proves existence of this common list, value one for every positive leaf
in either word, and value zero for every B-label when PA proves A and B
disjoint. `arithmetic_derivationValuation_PA` supplies the actual diagonal
alpha/beta instance using the existing PA disjointness proof. These statements
use actual successful-derivation predicates and arbitrary internal codes.

`membership_comparison_PA` proves agreement with the incoming
`ArithmeticFiniteLookup.graph` in PA and in every PA model. The two lookup
definitions and all four incoming finite-support and internal-induction
producers are preserved. The categorical support fold and numerical word
filter have their separate proved equations; equality of their numerical
outputs is not asserted.

## Verification and reconciliation

The [incremental verification record](V59_SIGNED_DERIVATION_FINITE_SUPPORT_VERIFICATION_2026-11-14.json)
records **21 successful commands**, including **13 strict elaborations**,
the project and both statement builds, parser tests, the v59
manuscript gate and both complete transitive axiom audits. All 41 principal
axiom reports and both complete audit unions use only `propext`, `Quot.sound`
and `Classical.choice`. The current audit covers
**946 modules and 28,963 declarations**; the retained audit covers **1,274**.

The tested proof commit is `7f85f8a7ea729741d852987eeae6c783a117f6a9`. All
2,445 measured inputs remained unchanged and match that commit. There are
fourteen expected input changes from the
[completed v59 full replay](V59_FULL_VERIFICATION_2026-11-14.md): nine new Lean
files, four production/audit entry files and the active correspondence table.
Every baseline input was independently compared with published proof commit
`8df18834734179186459d3c4c34d4c0cf20b6194`. All sixteen dependency worktrees
were clean and pinned at both ends; all 356 imported-source provenance checks passed.

Concurrent v59 work was fetched and merged without force. The four conflicts
were import lists; both sets of imports were preserved. The v58 correspondence
was restored as an archive, and the new support status was recorded in the
active v59 table. The incoming v59 manuscript, source archive, PDF, manifest
and AGENTS instructions retain their exact bytes. The reviewed v58 PDF and
archive and both unrelated Palomar files are preserved. The supplied Google
review and its existing assessment are retained; this proof batch adds no
manuscript correction or new whole-paper review claim.

The earlier 19-command v58 integration at `cb37dc3e11727a709ca38d07b3d9d4b98b3f757e` is
preserved as historical evidence. It finished before the v59 merge. The
1,798-command full v59 replay remains evidence for its own tested inputs;
**this new batch has incremental verification and no new full replay**.
Raw logs are retained in `.codex-work/v59-signed-derivation-20261114/`.

## Remaining argument

Construct the Boolean formula valuation in the slice over the finite support,
with truth the second coproduct injection and quantification the second
projection. Instantiate the existing substitution and seven-scheme laws.
Use `SyntacticDerivation.InternalInduction.model_rule_induction` on the definable truth
invariant for both proofs, covering generalization and modus ponens. Convert
the PA exclusion of contradictory conclusions to consistency of the printed
generated sentence subobject, then apply the existing signed-theory
essential-incompleteness criterion. Lemma 8.9 and Corollary 8.10 stay open
until those complete printed statements have independently checked proofs.
