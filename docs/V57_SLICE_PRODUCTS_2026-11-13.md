# Arbitrary partial-slice products and Turing structure for v57

Proof commit `647deeeb12d3309d2aede19592e6d7d61bd070c8` constructs binary restriction products of arbitrary
objects of the actual partial-map slice and proves its Turing property.
**Lemma 5.1 remains open** for the full constant-object recursion subcategory
and its restriction-splitting equivalence. There are **67 proved numbered
counterparts and ten open obligations**.

## Constructions

`V46RestrictionProductData` develops the partial pairing calculus for
chosen restriction products. `V46RestrictionProductCategory` derives all
fourteen `PCategory` laws and proves that the product-derived restriction
structure equals the existing one. `V46RestrictionProductComparison`
constructs the canonical total isomorphism between two product choices.

`V46AmbientSliceProducts` constructs products from pullbacks of total
families over T. Splitting a common partial domain proves that the
pullback projections detect equality of partial morphisms. The partial
cone lifting theorem supplies pairing, with its restriction, projection
and reconstruction equations. `V46PartialSliceProducts` lifts the
construction through the full faithful span comparison into
`Par(Tot(C)/T,Mono)`, with all product and restriction laws.

`V46SliceProductTuring` compares the arbitrary products with the earlier
fixed-input products and proves comparison naturality along total
parameters. Its evaluator is the total comparison followed by the earlier
evaluator, whose ambient value is the associator followed by `1_T×τ`.
The resulting `IsTuringMorphism` theorem quantifies over every source
object and every partial morphism in the actual slice, with a total
parameter in that same slice.

`V46PartialSliceRetractions` supplies restriction terminal morphisms,
including partial naturality and uniqueness among total morphisms. It
lifts total embeddings into the constant universal family and their
partial retractions into the actual span quotient.
`V46PartialSliceSplitting` proves that every slice restriction idempotent
splits with a total inclusion. `V46SplitSliceTuring` derives both the
universal evaluator and total retractions for C=Split(R) directly from
the original recursion category. The explicit product restriction on
Split(R) agrees with the existing one by the previously proved equality.

The full subcategory on the original constant families still needs its
recursion-category structure and a functor proving the printed splitting
equivalence. The whole partial slice is not asserted to be isotype.

## Verification

All **25 incremental commands passed**, including **18 strict commands**.
The selected axiom checks contain **74 reports**, including **36 for the
new constructions**.
The project and both statement entry points were rebuilt. Strict checks
cover all nine new producers, their combined statement checks, four
selected existing interfaces/check modules, the project entry point,
both statement audits and the current axiom audit. The retained statement
and axiom audits also passed.

The complete transitive audits cover **890 current production modules**,
**27,874 current declarations** and **1,274 retained declarations**.
Both axiom unions are exactly `propext`, `Quot.sound`, `Classical.choice`.
All sixteen dependency worktrees were clean and pinned at both ends;
all 356 imported-source comparisons passed.
All 2,377 measured inputs match the tested commit
and were unchanged during verification. The resume drift check found no
unexpected change in the 2,367 previous
measured inputs.

The [machine-readable record](V57_SLICE_PRODUCTS_VERIFICATION_2026-11-13.json) includes the exact commands,
log hashes, tested snapshot, baseline evidence and proof status. Raw
logs remain at `.codex-work/v57-slice-products-20261113/incremental-verification`.

- Source snapshot SHA-256: `740e999364a17d024de87d37d16aee0a16aa42edbf194efd82fc5236f0af1a22`.
- Raw verification JSON SHA-256: `022c982ae17de05700cfac98015118bf3d1606754b36c4194b4a4d2ef6ff1e3a`.

This is incremental verification. The earlier full 1,708-command replay
and all earlier incremental evidence remain preserved. The active
manuscript remains v57; source, PDF, source archive, manifest and current
instructions retain their previous bytes. The unrelated Palomar workflow
and declaration notes were preserved.
