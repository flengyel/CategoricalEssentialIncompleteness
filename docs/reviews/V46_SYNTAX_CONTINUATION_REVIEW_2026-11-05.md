# Author-side review of the syntax and soundness continuation

Scope: the new arithmetic source/check files after verified main `0c44cdafed27`, the manifest-selected current manuscript target, their required imports,
correspondence rows and the existing implementation/verification records.
This follows the HostileRefereeGPT — Cat/Rec instructions and includes
collaborating-agent source/type checks. It is not an independent whole-paper
review or an independent kernel certification.

The independent review of `3f53b33` inspected source and recorded verification
evidence; it did not independently rerun Lean or establish v46 completion.
It found no confirmed mathematical drift in that snapshot. Its findings have
been retained as distinctions to prove, rather than treated as a completion
certificate. The current v47 manuscript was integrated from the manuscript chat; Codex made no editorial source changes.

## (A) Kill-shots / hard blockers

No mathematical counterexample or confirmed hypothesis drift was found in
the inspected new endpoints. Initiality in 5.5/5.8 remains the full universal
property for the manuscript polynomial, arbitrary parameter families and
original typed rule pullbacks. The new native algorithm/categorical fold
comparison, success pullback, standard soundness factor and arithmetic
ultrapower instance are proved with their intended effective hypotheses.
The application dependencies below still prevent a whole-current-manuscript completion claim.

## (B) Major weaknesses

1. **The indexed-family fiber universal property remains open.** Anchor:
   `prop:arithmetic-theory-fibers`. `ArithmeticIndexedAxioms.axiomGraph`,
   `carrier_numeral`, `productIso` and `axioms` construct the literal family
   and its actual product-chart mono. `ArithmeticIndexedFamily.initial`
   proves initiality of the constructed whole family. The printed numeral
   fibers still require the extensive slice/algebra decomposition, the
   inference natural isomorphism, the per-e initiality comparison and the
   sentence-conclusion pullback square. Full-family initiality is not the
   required numeral-fiber universal property.

2. **The concrete arithmetic proof-system comparison is now proved.**
   `ArithmeticNamedAxiomComparison.axiomsAdmissible_PA` discharges the
   source-axiom premise from the actual native PA arithmetic/order and
   arbitrary-induction axioms with finite universal closure. The proved
   numeral-convention transport and native finite-proof realization yield
   the standard Γ bounds. Their fixed universal closures transfer to every
   M≡N, and `ArithmeticDiagonalRepresentation.printed_representation`
   proves the proper sentence-object inequalities of 7.1. The semantic
   model K is constructed from native consistency; its actual soundness
   factor and ultrapower transport discharge the target consistency
   conditions. `ArithmeticInternalComparison.internal_comparison` and
   `total_undecidable_family` prove the categorical 7.3 application and its
   total source family. No source-admissibility, assumed soundness factor,
   PA consistency proof or imported arithmetic incompleteness theorem is
   used as a replacement for these steps.

3. **Later applications remain separate.** Indexed-family numeral-fiber
   and uniform-presentation comparisons, numerical inference realization,
   representation-independent Miller computation and cosheaf derivation
   initiality remain open as recorded in the correspondence table. The completed numerical tuple comparison 7.7 is not listed as open;
   rows 9.1 and B.10 retain their corrected wording.

The direct Corollary 7.4 application is also proved: an actual recursive
Θ-preimage and partial source conditional contradict categorical Corollary
3.2; the c.e. parallel-enumeration proof and native finite axiom replacement
give closed-sentence and extension incompleteness. Its final statement
contains only the printed Γ PA-derivability and consistency hypotheses.

## (C) Minor issues

**Elaboration dependencies were repaired without changing mathematics.**
Local notation in concrete `variable` declarations hid dependencies on
signature parameters and semantic operations, producing apparent graph-type
normalization failures. Fully written dependent binder types and explicit
section-variable inclusion resolve the concrete soundness construction.
Abstract model-predicate lemmas expose raw graph conditions through proved
iff statements and have literal algebra/carrier/conclusion equalities to the
existing generated-theory data. They do not supply an assumed evaluator,
initiality or soundness factor. Targeted reduced-budget diagnostics and all
failed snapshots/logs are preserved; no Lean limit or linter was disabled.

**Only verified production layers count.** The concrete arithmetic axiom/model/comparison chain and the full indexed-family construction have passed targeted production and strict checks. Uncompiled extensive-fiber, uniform-presentation and optional expanded-chart drafts remain separate. The freeze receipts and exact declarations are listed in the existing continuation report.
The final verification record identifies the exact tested and committed
source bytes and any new component subsequently completed.

The new realization comparison is proved for arbitrary T extending PA,
predicate codomain and T-supported, T-total graph, before specialization to
the arithmetic formula. Explicitly typed predicate objects preserve the
original carrier. Reduced diagnostic limits exposed elaboration problems;
no production limit was raised. The literal Total sentence morphism has its
actual all-PA-model graph and value comparison. Its additional expanded
source-projection drafts remain preserved and are not used as a substitute
for a proved equation.

## (D) Cross-section consistency

- The original named polynomial, labels, ordered children and parameter
  families are preserved. Arbitrary algebra operations require their actual
  T-supported total graphs, not primitive-recursive or PA-total operations.
  Initiality adds no consistency, c.e., soundness or standardness hypothesis.
- The actual computed substitution is a proved algebra morphism; stable
  initiality identifies it with the fold. Its success pullback is identified
  with the independent free-for recursion. The equal-binder branch keeps the
  original body even if recursive substitution fails.
- Every rule child has its own prescribed conclusion; the parent conclusion
  is induced by the rule's conclusion map. Nullary rules need no global
  formula point. Standard reverse finite-tree comparison requires N models T;
  no nonstandard Set initiality is asserted.
- Formula-image/sentence/source-idempotent assembly uses the constructed
  syntax, lists and arbitrary-rule initiality. Chosen pullback and inverse
  equivalence codes are not assumed to be original formula codes or primitive
  recursive charts.
- Standard soundness uses the actual seven parameter families, both rules,
  constructed derivation induction, actual sentence pullback and unique
  validity corestriction. Only nonlogical axiom validity is assumed.
  Semantic K and arithmetic code models N/M remain distinct; disjointness
  retains nonempty K.
- The arithmetic-ultrapower instance supplies the proved standard factor and
  the constructed canonical comparison. It derives factorization and
  conclusion-image consistency, rather than assuming a comparison or factor.
- Exponential/parity object coding and the uniform computation comparison are
  separate completed proofs. Native comp/s certificates accompany full
  all-internal PA graph laws; k_e is an actual PA-total program. Production
  graph equality is proved in PA at fixed external indices on all internal
  inputs, with no arbitrary-index stage-persistence assumption.

## (E) Verification and disposition

The baseline full verification exited 0 in `.codex-work/verify-20261106T052422Z-MLM1qM`; all 837 commands passed.
The permitted axiom union and clean pinned dependencies were checked. All
1119 tested input hashes match proof commit `16ec62198d0aaa6506fc50d949f35af0fb26d94d`, whose ordinary
main push and remote ref were confirmed. The delivery receipt records the
separate report commit and six copied-byte hashes.

Full verification exited 0 in `.codex-work/verify-20261106T125901Z-Acu0zJ`; all 905 commands passed.
The permitted axiom union and clean pinned dependencies were checked. All
1187 tested input hashes match proof commit `e08d21c7eee33e6e7ee398411124039133a92905`, whose ordinary
main push and remote ref were confirmed. The delivery receipt records the
separate report commit and six copied-byte hashes.

An earlier full replay returned exit 1 only after the 905 successful Lean
commands: the lexical gate matched an English word in a documentation
comment. The comment-only repair and complete successful rerun are recorded;
no proof, statement, axiom or verifier condition was relaxed.

The scoped source/type review supports the stated completed endpoints and
explicit remaining obligations. It does not replace the kernel/axiom checks,
certify the whole current manuscript or revise the manuscript to weaken the target statements.
