# Proposition 10.8: uniform finite propositional derivations

All seven erased first-order logical schemes now have uniform finite
derivations in the original propositional fork proof carrier. They assemble
into one natural morphism, with the prescribed original conclusion, and
factor through the actual propositional theorem image. This is partial
progress within Proposition 10.8. The count remains **75/77**; Proposition
10.8 and Corollary 10.9 remain open. Manuscript v59, its source, PDF,
archive and manifest are unchanged.

## Construction

`V46PropositionalProofCombinators` constructs derivations as morphisms
on arbitrary parameter objects with their conclusion equations. Ordered
modus ponens uses the actual rule-input pullback, retaining the children
H and H ⇒ K in that order. Its identity construction is the printed
derivation of H ⇒ H from the first two schemes with exactly two MP
applications. Weakening is another finite construction from the first
scheme and MP. The helper scheme witnesses are filled concretely below.

`V46PropositionalSchemeTransport` proves the three scheme equations
under the actual product comparisons of a finite-product-preserving
functor. It retains the ordered binary and ternary parameter objects.
For the fork realization these preservation instances come from the
existing equivalence.

`V46ForkPropositionalProofs` identifies the three logical coefficients
of the original Fin 5 axiom presentation with the corresponding
propositional expressions. Its three witnesses use the actual coproduct
injections, the existing axiom-shape isomorphism and the existing proof
algebra. Uniform identity and weakening land in the original realized
finite-tree carrier. In particular the printed global p_* ⇒ p_* has
a global finite derivation.

`V46ForkErasedSchemeProofs` combines those witnesses with the already
proved erasure equations. The first three schemes use the corresponding
nullary rules. Instantiation and distribution use uniform identity,
reflexivity uses the global tautology proof, and equality substitution
uses identity followed by weakening. All actual scheme parameter objects
are retained, including the instantiation success pullback, distribution
absence fiber and both equality-substitution success pullbacks.

The seven morphisms assemble over the actual logical-parameter coproduct:

```
logicalProof.hom ≫ realization.map originalConclusion = logicalAxioms ≫ erase
```

The construction quantifies over arbitrary signed axiom domains a,b and
arbitrary formula parameter diagrams. Its final fork statement has no
derivability, initiality or compatibility hypothesis. The proof morphism
is natural under every fork transition, including atom-identifying
transitions. Composing it with the regular-image factorization proves
that every erased logical instance factors through the actual theorem
image. All original carrier, product, coproduct and conclusion comparisons
are reused; inverse-equivalence numerical charts are never identified.

Independent `V46ForkErasedSchemeProofsChecks` restates all seven derivation
statements, the single uniform conclusion equation, naturality and image
factorization. It also checks ordered MP, the exact two-MP identity
construction, weakening and the actual scalar-code carriers and
coefficients. There are 32 principal permitted-axiom reports. All four
producers and the independent checks are integrated in the current entry
points and audits.

## Verification

The tested proof commit is `bb501397079cc20717e420d44e3ceb6db676e888`. All five selected
producer/Checks sources pass strict elaboration with warnings as errors,
2 GB memory and a 120-second timeout per source. The subsequent
**17-command incremental verification** passes all nine strict commands,
the combined build, current and retained statement audits, parser tests,
manuscript gate and both complete transitive axiom audits.
The current audit covers **1055 production modules**
and **31530 declarations**; the retained audit covers
**1274 declarations**. Both audits and all 32 selected
reports use only `propext`, `Quot.sound` and `Classical.choice`.

All **2587 measured inputs** match the committed
proof snapshot and are unchanged after verification. All 16 dependency
worktrees remain clean at their pins; all 356
source-provenance records pass. Runs use the serial build lock and one
Lean thread. Integrated strict commands use 3 GB; the complete current
axiom audit has a 900-second timeout. Development failures are retained
separately and excluded from the successful targeted and integrated runs.

The [verification record](V59_UNIFORM_PROPOSITIONAL_DERIVATIONS_VERIFICATION_2026-11-17.json) includes command and log hashes,
targeted checks, dependency state and the measured delta from the previous
successful incremental batch. The full local record is
`.codex-work/v59-uniform-propositional-proofs-20261117/incremental-verification/verification.json`,
SHA-256 `ff7004edd65724208a211a744ab45d3a76714e15b62a080082bacca75687c994`.

This is completed incremental verification of the uniform derivation
construction. No new full replay was run. The last completed full replay
remains the 1,798-command v59 replay at
`8df18834734179186459d3c4c34d4c0cf20b6194`, including 1,792 strict
elaborations. The reviewed v58 artifacts, WSL recovery archive and
unrelated local files are preserved.

## Exact continuation point

Continue Proposition 10.8 with the inference and generated-theory
comparisons. `ForkErasedSchemeProofs.logicalProof` supplies the uniform
logical derivations, and `image_factor` supplies their factorization
through the actual propositional theorem image. Generalization erases
to its premise; modus ponens is compared using the proved implication
equation. Construct closure of the erasure pullback of the propositional
theory, then apply leastness of the generated first-order formula theory.
Construct the reverse inclusion using the proved propositional embedding
and actual derivation translations.

Generation of an arbitrary signed axiom morphism must pass through its
regular image. Required initiality remains indexed only by axiom
subobjects. Prove conservativity and consistency, then reduce the original
inseparable domains along the first-order atomic constructor and apply
domain incompleteness. The endpoint statement must cover every consistent
c.e. extension at the selected endpoint without requiring an extension
family on the whole fork. Proposition 10.8 stays open until every printed
clause and independent statement check has passed.

For Corollary 10.9 reuse completed Theorems 5.2–5.3, the constructed
all-parameter deduction, actual restriction comparisons and a common
global logical theorem. Preserve arbitrary closed consistent slice
extensions, including nonconstant families. Keep v59 unchanged unless an
actual mathematical defect is established.
