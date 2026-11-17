# Proposition 10.8: substitution invariance and erased schemes

Admissible substitution preserves the actual fork erasure. The stronger
Option-valued equation also preserves substitution failure. All seven
logical schemes have the erased expressions printed in Proposition 10.8.
This is partial progress: uniform propositional derivations and the
generated-theory arguments remain open. The count remains **75/77**.
Manuscript v59 and its source, PDF, archive and manifest are unchanged.

## Construction

`V46NullaryErasureSubstitutionSteps` extends the existing substitution
constructor argument to erasure into an arbitrary propositional carrier
and operations. Equality has the fixed value, nullary atoms are retained,
negation and implication preserve the inductive invariant, and
quantification erases to the second projection. The quantifier step
retains both the variable-equality and capture-allowed Boolean branches.
It does not test equality of formulas or require atom-label injectivity.

`V46NullaryErasureSubstitutionInvariant` constructs the two morphisms
whose equalizer expresses the invariant over the actual substitution
parameter object. Every constructor preserves that equalizer.
`V46NullaryErasureSubstitution` uses the proved parameterized initiality
and equalizer induction to establish

```
formulaSubstitutionOption ≫ OptionSyntax.map erase =
  OptionSyntax.mask (prod.fst ≫ erase) formulaSubstitutionOption
formulaSubstitution ≫ erase = admissibleInclusion ≫ prod.fst ≫ erase
```

The first equation preserves the failure flag, including failed
capture-avoiding substitutions. The second is the printed admissible
substitution invariant. The existing Boolean substitution modules are
unchanged; Boolean valuation is not substituted for propositional erasure.

`V46ErasureLogicalSchemes` calculates the erasure of all seven schemes
on their actual parameter objects. The first three are the corresponding
propositional expressions. Instantiation, distribution, reflexivity and
equality substitution erase respectively to H ⇒ H,
(H ⇒ K) ⇒ (H ⇒ K), the fixed global tautology, and
top ⇒ (H ⇒ H). Instantiation retains its success pullback,
distribution retains the absence fiber, and equality substitution retains
the intersection of both success pullbacks. Their projections identify
the same original formula before erasure.

`V46ForkErasureSubstitution` specializes all these equations to the
constructed fork syntax and actual erasure, using the original
coefficient diagram and propositional object. Substitution erasure is
natural under every fork transition, including transitions that identify
atoms. The previously proved embedding and retraction are reused.

Independent `V46ForkErasureSubstitutionChecks` checks the full generic
and fork statements, arbitrary local successful substitutions, failure
preservation, all seven scheme expressions, actual coefficients and the
embedding retraction. It includes 32 principal permitted-axiom reports.
All five producers and the independent checks are integrated in the
current entry points and audits. These are calculations of expressions;
no uniform propositional derivability or incompleteness conclusion is
assumed or reported as proved.

## Verification

The tested proof commit is `7214cd7e02f1825362b4d191141b638f0590988b`. All six selected
producer/Checks sources pass strict elaboration with warnings as errors,
2 GB memory and a 120-second timeout per source. The subsequent
**18-command incremental verification** passes all ten strict commands,
the combined build, current and retained statement audits, parser tests,
manuscript gate and both complete transitive axiom audits.
The current audit covers **1051 production modules**
and **31388 declarations**; the retained audit covers
**1274 declarations**. Both audits and all 32 selected
reports use only `propext`, `Quot.sound` and `Classical.choice`.

All **2582 measured inputs** match the committed
proof snapshot and are unchanged after verification. All 16 dependency
worktrees remain clean at their pins; all 356
source-provenance records pass. Runs use the serial build lock and one
Lean thread. Integrated strict commands use 3 GB; the complete current
axiom audit has a 900-second timeout. The initial development check ended
with exit 124; its empty log is retained. A traced development check and
a later scheme-normalization failure are retained separately. None is
counted among the successful targeted or integrated commands.

The [verification record](V59_ERASURE_SUBSTITUTION_SCHEMES_VERIFICATION_2026-11-17.json) includes command and log hashes,
targeted checks, dependency state, development-failure records and the
delta from the preceding successful incremental batch. The full local
record is
`.codex-work/v59-erasure-substitution-20261117/incremental-verification/verification.json`,
SHA-256 `fa718e8a06c743448867d954fb388558fc598c21ef611136c925e66d18a6b6bd`.

This is completed incremental verification of substitution invariance and
the seven erasure calculations. No new full replay was run. The last
completed full replay remains the 1,798-command v59 replay at
`8df18834734179186459d3c4c34d4c0cf20b6194`, including 1,792 strict
elaborations. The reviewed v58 artifacts, WSL recovery archive and
unrelated local files are preserved.

## Exact continuation point

Construct uniform finite propositional derivations of the seven erased
scheme expressions. In particular build H ⇒ H from the first two
schemes and two applications of modus ponens as printed, then instantiate
it and weaken it for the remaining erased schemes. Use the actual
`ForkDerivation.Diagram.inferenceAlgebra` and its Fin 5 axiom presentation,
with the proved product and coproduct comparisons. The erasure equations
are in `V46ForkErasureSubstitution`. The truth morphism is exactly the
printed global p_* ⇒ p_* from `V46ForkFirstOrderErasure`.

Use those derivations for the inference and generated-theory comparison.
Generation of an arbitrary signed axiom morphism must pass through its
regular image; required derivation initiality remains indexed only by
axiom subobjects. Prove conservativity and consistency, then reduce the
original inseparable domains along the first-order atomic constructor
and apply domain incompleteness. The selected-endpoint conclusion must
cover every consistent c.e. extension at that endpoint without requiring
an extension family on the whole fork. Only after every printed clause
and independent statement check passes may Proposition 10.8 be marked
proved.

Corollary 10.9 remains next. Reuse the completed Theorems 5.2–5.3,
constructed all-parameter deduction, actual restriction comparisons and
a common global logical theorem. Preserve arbitrary closed consistent
slice extensions, including nonconstant families, and all permitted-axiom
checks. Keep v59 unchanged unless an actual mathematical defect is
established.
