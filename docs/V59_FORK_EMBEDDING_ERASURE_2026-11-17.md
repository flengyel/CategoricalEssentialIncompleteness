# Proposition 10.8: natural embedding and erasure

The natural propositional sentence embedding and first-order erasure are
constructed, with the printed retraction equation and monicity. This is
partial progress within Proposition 10.8. The count remains **75/77**;
Proposition 10.8 and Corollary 10.9 remain open. Manuscript v59, its source,
PDF, archive and manifest are unchanged.

## Proved construction

`V46NullaryPropositionalErasure` constructs erasure from the complete
nullary first-order syntax into arbitrary propositional operations.
It proves all five constructor equations, uniqueness among all underlying
formula morphisms satisfying those equations, and compatibility with
morphisms preserving the target operations. Equality has a fixed value
and quantification is the second projection.

`V46ForkFirstOrderErasure` specializes this construction to the actual
universal coefficient diagram V and the existing propositional formula
object S. It uses the original total-fork realization equivalence. The
zero quadruple and its zero-pair endpoint images provide the printed
global atom p_*. Equality erases to exactly p_* ⇒ p_*. The erasure is a
natural morphism of fork diagrams; all five constructor equations and raw
uniqueness are proved.

`V46ForkPropositionalFolds` reuses the original recursive propositional
fold in the total fork category. It proves the natural comparison between
the original coded product and the chosen categorical product, then
transports folds through the full and faithful numerical-diagram
realization. Every target diagram and every underlying morphism satisfying
the three constructor equations is covered. The counit isomorphism is
retained explicitly; inverse-equivalence numerical charts are never
identified.

`V46ForkPropositionalEmbedding` constructs the embedding directly into
the first-order sentence pullback, including implication closure of
sentences. It preserves atoms, negation and implication. With Lean's
left-to-right composition, the proved retraction is
`embedding ≫ sentenceInclusion ≫ erase = 𝟙 sentences`.
Consequently the sentence embedding is monic. Both morphisms are natural
under every fork transition, including transitions that identify atoms.

Independent `V46ForkFirstOrderErasureChecks` checks the actual coefficient
and propositional carriers, zero scalar coordinates, global point,
printed tautology, five erasure clauses, raw uniqueness, three embedding
clauses, sentence factorization, retraction, monicity and naturality.
It also checks the propositional fold's universal property for arbitrary
target diagrams. There are 24 selected transitive permitted-axiom reports.
All four producers and the independent checks are integrated in the
current entry points and audits.

## Verification

The tested proof commit is `afd721cc59bb4454744eddda019b8c1344bd080e`. The five selected
producer/Checks sources pass targeted strict elaboration with warnings
as errors, a 2 GB memory limit and a 120-second timeout per source.
The subsequent **17-command incremental verification** passes all nine
strict commands, both complete transitive axiom audits, the parser tests,
manuscript gate, combined build, current and retained statement audits.
The current audit covers **1046 production modules**
and **31316 declarations**; the retained audit covers
**1274 declarations**. Both audits and all 24 selected
reports use only `propext`, `Quot.sound` and `Classical.choice`.

All **2576 measured inputs** match the committed
proof snapshot and are unchanged after verification. All 16 dependency
worktrees remain clean at their pins; all 356
source-provenance records pass. The runs use the serial build lock and
one Lean thread. Integrated strict commands use 3 GB; the complete current
axiom audit has a 900-second timeout. Development failures are retained
separately and are not counted as successful verification commands.

The machine-readable [verification record](V59_FORK_EMBEDDING_ERASURE_VERIFICATION_2026-11-17.json) records command and log
hashes, targeted checks, dependency state and the delta from the preceding
successful incremental batch. The full local record is
`.codex-work/v59-fork-erasure-20261117/incremental-verification/verification.json`,
SHA-256 `2838b509c012e49279899b155c832cc3e490d41499d8804b02d9a6993cec6308`.

This is completed incremental verification of the syntax comparison.
No new full replay was run. The last completed full replay remains the
1,798-command v59 replay at
`8df18834734179186459d3c4c34d4c0cf20b6194`, including 1,792 strict
elaborations. The WSL recovery archive and unrelated local files are
preserved verbatim.

## Exact continuation point

Continue Proposition 10.8 with admissible-substitution erasure invariance:
`firstOrder.formulaSubstitution ≫ erase =
firstOrder.admissibleInclusion ≫ prod.fst ≫ erase`.
Reuse the constructed fold and five erasure clauses. The existing
`V46NullaryBooleanSubstitutionSteps`, `V46NullaryBooleanSubstitutionInvariant`
and `V46NullaryBooleanSubstitution` supply the Option-mask and equalizer
induction pattern; the new target is the actual propositional formula
object, so Boolean valuation alone does not discharge this obligation.

Then prove that erasure sends the first three logical schemes to their
propositional counterparts and the remaining four to the uniformly
derivable printed tautologies. Use the completed all-parameter deduction
and existing rule translations for the inference and generated-theory
comparisons. Prove conservativity, consistency, internal essential
incompleteness and every endpoint extension conclusion before changing
the numbered status. The endpoint extension is arbitrary at the selected
endpoint and need not extend to a global diagram.

For Corollary 10.9, reuse the completed Theorems 5.2–5.3, parameterized
deduction and a common global logical theorem. Preserve all arbitrary
closed consistent slice extensions, including nonconstant families.
Required initiality remains indexed only by axiom subobjects; arbitrary
axiom morphisms generate through their regular images. Do not add
preservation or incompleteness conclusions as hypotheses.
