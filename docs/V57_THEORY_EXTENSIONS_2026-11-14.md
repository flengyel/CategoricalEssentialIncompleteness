# Theorem 5.2: theory extensions and associated categories

Proof commit `f4572a09adb61331ae07e64da235e35cda23cb40` completes manuscript v57 Theorem 5.2.
Postcomposition and pullback on the actual monic partial-map slices have
both adjunctions Σ_i⊣i*⊣Σ_i. Postcomposition is fully faithful and
restriction preserving, with the printed sentence and theorem comparisons.
The count is **69 proved numbered counterparts and eight open obligations**.
The first open result is Theorem 5.3.

## Constructions

`V46PartialSlicePostcompose` retains the base morphism of each partial
family morphism. Monicity of the total inclusion i and its partial inverse
give fullness; faithfulness and restriction preservation hold directly.
`V46PartialSliceReindex` constructs pullback on families using the previously
proved arbitrary binary restriction products. Its first projection detects
partial morphisms over T, which supplies the uniqueness used in both
adjunctions.

`V46PartialSliceLeftAdjunction` constructs the first natural hom equivalence
by pairing a morphism with its total projection. For the second equivalence,
`V46PartialSliceRightAdjunction` proves that a partial morphism into an image
object has domain contained in the pullback inclusion. Its partial inverse
then extends a morphism out of the pullback. The inverse laws and naturality
in both variables are proved before constructing the adjunctions.

`V46PartialSliceChangeBase` defines postcomposition as the partial-map
functor induced by `Over.map i`, so it literally retains each span.
It defines reindexing through the proved family equivalence and realization.
`V46PartialSliceSpanPullback` proves equality with the partial-map functor
induced by `Over.pullback i`. The proof checks total morphisms and inverses
of total monomorphisms, then uses the factorization of every partial span
into those two generators. Thus the resulting functor pulls back each apex
and both legs of every span.

`V46PartialSliceAdjunctions` transports both natural hom equivalences into
Par(D/T) and Par(D/U), constructing the actual adjunctions. The second unit
is proved equal to the literal partial inverse of the pullback inclusion.
For proper i, its component at the terminal family is non-total.
`V46PartialSliceProperness` proves that an isomorphism from an image object
to the terminal family would make i invertible, giving failure of essential
surjectivity. `V46PartialSliceSpanChangeBase` proves identity and composition
as equalities of functors. `V46PartialMapFunctorComposition` supplies the
generic identity, composition and congruence results for induced functors.

`V46PartialSlicePostcomposeProducts` constructs a binary restriction-product
isomorphism in the actual partial slice, with both projection equations.
Its underlying total pullback comparison follows from monicity of i.

`V46PartialSliceTheoryComparison` and `V46PartialSliceTheoryFamilies` construct
the total comparison morphisms i×id_S and i×i, prove the printed square for
i≫u=t, and construct the sentence-family isomorphism. Transposing the square
gives a total factorization of the source theory through the pulled-back
theory. `V46PartialSliceTheorySubobjects` proves the corresponding inequality
of subobjects in Tot(Par(D/T)), after identifying the sentence families.

`V46TheoryExtensionsChecks` checks all these clauses at their explicit
intended types, including the action on spans, ordinary pullback, both
adjunctions, properness, composition, total comparison morphisms and their
raw values, the square, sentence isomorphism and actual subobject bound.
The construction uses the printed total-monomorphism partial inverses,
splitting and total pullbacks. These are supplied by the manuscript's
hypotheses on C=Split(R) and regular D=Tot(C); syntax and deduction are not
needed for this categorical construction.

## Verification

All **30 incremental commands passed**, including
**23 strict commands**. The selected axiom checks
contain **125 reports**, including
**51 in the assembled Theorem 5.2 checks**.
The project and both statement entry points were rebuilt. Strict checks
cover all fourteen new producers, the assembled checks, four existing
interfaces/check modules, the root, both statement audits and the current
axiom audit. Both retained audits also passed.

The complete transitive audits cover **913
current production modules**, **28,307 current
declarations** and **1,274 retained declarations**.
Both axiom unions are exactly `propext`, `Quot.sound`, `Classical.choice`.
All sixteen dependency worktrees were clean and pinned at both ends;
all 356 imported-source and
4 retained manuscript provenance
comparisons passed. All 2,402 measured inputs match
the tested proof commit and were unchanged during verification. The drift
check found no change in the 2,387 previous
inputs before this work.

The [machine-readable record](V57_THEORY_EXTENSIONS_VERIFICATION_2026-11-14.json) contains the commands, log hashes,
source snapshot, baseline evidence and proof status. Raw logs remain at
`.codex-work/v57-theory-extensions-20261114/incremental-verification`.

- Source snapshot SHA-256: `8442d7960066fd0db38206fd95033893899b52b305552038588da03eeb441efb`.
- Raw verification JSON SHA-256: `693eb90cf57b55dd8501e20c7e9802ebf1a111e53eb440e701e7a4cb4ccb22fd`.

This is incremental verification. The earlier full 1,708-command replay and
all earlier incremental evidence remain preserved. The active manuscript
remains v57; source, PDF, source archive, manifest and current instructions
retain their previous bytes. The unrelated Palomar workflow and declaration
notes were preserved.
