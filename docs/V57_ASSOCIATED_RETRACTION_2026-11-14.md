# Theorem 5.3: evaluation retraction and Boolean partial morphisms

Proof commit `f147a49ecddc87509b02156a912b0b0dbbdbce68` constructs the constant-family/evaluation
retraction and proves the two Boolean-morphism equivalences in manuscript
v57 Theorem 5.3. The theorem remains open: transfer of closed sentence
theories and the full essential-incompleteness equivalence still require
proof. The count remains **69 proved numbered counterparts and eight open
obligations**.

## Constructions

`V46ConstantFamilyRetraction` proves naturality of the sentence-family
comparison for arbitrary partial morphisms. It constructs a natural
isomorphism from constant families to their pullbacks along a total mono.
A global point from a terminal total object is monic. Pullback along that
point, followed by forgetting the terminal projection, evaluates a family.
The terminal-product isomorphism and the pullback comparison give a natural
retraction on constant families.

`V46AssociatedEvaluation` realizes this construction on the actual monic
partial-map slice Par(D/U). It proves that evaluation equals ordinary span
pullback followed by the base functor and constructs E_UB_U≅id_C as a
natural isomorphism. Both functors preserve restrictions. The global point
is exactly the factorization supplied by the manuscript's logical theorem;
no complementedness hypothesis is imposed on that inclusion.

`V46RestrictionRetraction` proves a general result for restriction functors
B and E with BE naturally isomorphic to the identity. B is faithful and
reflects totality. An actual total morphism g extends f precisely when
rst(f)≫g=f. A total extension of B(f) gives one of f by applying E and
conjugating by the natural isomorphism. Thus existence of total extensions
is preserved and reflected, with an explicit reflected morphism.

`V46BooleanPartialDecision` constructs a Boolean partial morphism for any
disjoint pair a,b of total subobjects. The left leg of its span is the
monic copairing of their inclusions; the right leg gives true on a and false
on b. Both values are proved. Its restriction is the domain idempotent
corresponding to a⊔b, and the morphism is total exactly when a⊔b is top.
Total extensions correspond exactly to complementary-subobject separators.
The proof works in an arbitrary restriction category whose total category
is regular and finitary extensive, with the stated monic partial inverses.

`V46AssociatedBooleanDecision` applies this construction to a consistent
theory and its refutation subobject. It proves the printed equivalences
between incompleteness and non-totality of the associated Boolean morphism,
and between source inseparability and absence of a total extension in the
actual associated category. The second statement is checked both for total
subobjects and for the source restriction idempotents under the existing
proved subobject/domain identification. The generic disjoint-pair result
also applies independently of the first-order presentation.

`V46AssociatedExtensionWitness` proves that every consistent extension
receiving a total subobject reduction of an inseparable pair has the
associated no-total-extension witness. Pullback of any proposed separator
would contradict the source inseparability.

`V46AssociatedCategoryChecks` checks the retraction, ordinary pullback,
restriction preservation, faithfulness, totality/extension comparisons,
Boolean values and domain, both Boolean equivalences and extension witnesses
at explicit types. In the theory statements the associated parameter is
the literal carrier of the theory subobject, and the supplied point factors
through that carrier.

## Remaining obligation

Theorem 5.3 still requires transfer of closed sentence theories under B_U
and E_U using the assumed parameterized syntax and initial finite derivation
algebras. The corresponding consistency and completeness preservation and
the full essential-incompleteness equivalence, including its conclusion for
consistent extensions, remain open. No closure-preservation field is added
to substitute for this proof.

## Verification

All **22 incremental commands passed**, including
**15 strict commands** and both complete transitive
axiom audits. Selected checks contain **125
reports**, including **35 in the new
subgoal checks**. The project and both statement entry points were rebuilt.
Strict checks cover all six new producers, their assembled checks, four
selected existing interfaces/check modules, the root, both statement entry
points and the current axiom audit. Both retained audits passed.

The current transitive audit covers **919
production modules and 28,383 declarations**;
the retained audit covers **1,274 declarations**.
Both axiom unions are exactly `propext`, `Quot.sound`, `Classical.choice`.
All sixteen dependency worktrees were clean and pinned at both ends.
All 356 imported-source and
4 retained manuscript provenance
comparisons passed. All 2,409 measured inputs match
the tested proof commit and stayed unchanged during verification. The drift
check found no change in the 2,402 previous
inputs before this work.

The [machine-readable record](V57_ASSOCIATED_RETRACTION_VERIFICATION_2026-11-14.json) contains the command details,
log hashes, source snapshot and proof status. Raw logs remain at
`.codex-work/v57-associated-retraction-20261114/incremental-verification`.

- Source snapshot SHA-256: `a1edcfe836d6a1441e8dd92dabb77b4927b9ed179f8c06f23a0a410c42699a30`.
- Raw verification JSON SHA-256: `920f43641447a1e92f9a3f2ea7c0232d14c6b6dbc53e76dd0d540d1deb12c345`.

This is incremental verification. Earlier full and incremental evidence
remain preserved. The manuscript remains v57, with unchanged source, PDF,
source archive, manifest and current instructions. The unrelated Palomar
workflow and declaration notes were preserved.
