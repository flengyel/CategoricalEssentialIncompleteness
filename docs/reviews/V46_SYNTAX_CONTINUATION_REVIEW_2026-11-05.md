# Author-side review of the syntax and derivation continuation

Scope: the new Lean constructions and changed correspondence rows since
`3f53b33d647940d0429679db192f3ea689b8a5d4`, with the preceding verified
checkpoint retained in the verification record. This is an author-side
review under the HostileRefereeGPT — Cat/Rec instructions, including scoped
source/type reviews by collaborating agents. Targeted production builds and
strict statement checks passed. The complete integration audit passed all 386 commands and the
expanded transitive axiom audit; exact evidence is in the verification JSON. This review does not
claim an independent kernel replay or whole-manuscript certification.

The independent review supplied for `3f53b33` inspected source and recorded
verification evidence; it did not independently rerun Lean. It found no
confirmed mathematical drift in that snapshot and did not establish completion
of v46. It required constructor compatibility and uniqueness among algebra
morphisms for 5.5, the arbitrary-signature universal property for 5.8, and the
categorical soundness/comparison chain for the arithmetic application.
Exponential object coding was already completed; the uniform trace bridge
remains separate. The stale 9.1/B.10 tuple-comparison wording is corrected.
Manuscript prose revisions remain deferred.

## (A) Kill-shots / hard blockers

No mathematical hard blocker was confirmed in the completed new constructions.
Proposition 5.5 now has the actual universal property in every parameter slice,
and Lemma 5.8 now has the universal property for the stated arbitrary inference
signature in the predicate and actual total split categories. The remaining
obligations below prevent a claim of complete v46 formalization.

## (B) Major weaknesses

1. **The full printed computation presentation remains unproved.**
   Anchor: §5, `05-syntactic-recursion-category.tex`, Lemma 5.1,
   `lem:arithmetized-evaluation`. Failure mode: **unproved**; evidence:
   **structural_argument**. The actual three-variable first-success graph has
   PA-proved functionality, exponential-input universal evaluation and a
   trace/output presentation at every internal index. Fixed-stage totality
   and the standard primitive-recursive output reader are proved. The trace
   predicate is currently exported as Sigma-one. Its primitive-recursive
   certificate and PA defining-graph comparison, uniform composition and
   specialization equations, and PA-total parameter-index programs remain
   required. The completed exponential/parity object coding is separate.
   Downstream: exact printed computation-presentation identifications remain
   qualified. Severity: major for full completion; no counterexample is claimed.

2. **The numerical named-variable realization remains incomplete.**
   Anchor: Proposition 5.7, `prop:st-substitution-realization`, in
   `05a-internal-syntax.tex`. Failure mode: **unproved**; evidence:
   **absence_in_text** at the final concrete numerical endpoint. The actual
   stable syntax instance is now constructed. The remaining task is to prove
   the PA equations, preservation and primitive-recursive certificates for
   the concrete list/FV/substitution traversals, identify them with the folds
   and identify success with free-for substitution. The equal-binder branch
   retains the original body even if its recursive result failed. A decoded
   arbitrary T-total algebra does not itself supply PA-total or primitive-
   recursive numerical operations. Severity: major for the remaining logical
   realization; no false assertion has been established.

3. **The coded soundness and categorical arithmetic chain remains open.**
   Anchors: 5.9, 6.5–6.6, 6.9 and 7.1–7.3. Failure mode: **unproved**;
   evidence: **structural_argument**. Sentence-image charts, filtered program
   ranges and representing source idempotents are constructed. Final concrete
   generated-theory closure/leastness and the numerical sentence identification
   remain to be integrated. The standard named-tree semantic substitution and
   seven-scheme/rule validity lemmas are proved, but the full standard-code
   bijection, actual numerical-operation comparison and coded validity
   factorization/disjointness are still required. Only that proved factorization
   can instantiate the existing ultrapower transport. The Gamma predicates,
   interpreted diagonal bounds, partial proof-search lift and categorical
   comparison application remain necessary. Importing an arithmetic
   incompleteness theorem does not supply those identifications. Severity:
   major for full completion.

## (C) Minor issues

**Resolved elaboration normalizations.** New proofs needed explicit finite-
vector equalities, finite-power/arity reductions, opaque generic comparison
lemmas and named local instances. Default-budget normalization timeouts were
resolved without raising Lean's limits or adding mathematical hypotheses.
Failed elaboration logs and useful continuation drafts remain preserved.
These repairs change the new proof elaboration, not manuscript definitions.

**Dependency-worktree check completed.** The existing verifier previously
checked revisions after building. It now records revisions and tracked/
untracked worktree status before building and after the axiom audit, rejects
changes and preserves them. A temporary Git fixture checked clean acceptance,
tracked/untracked rejection, preservation and revision mismatch rejection.
All 16 pinned dependency worktrees passed the current preflight. This is an
extension of the existing verifier, not a new verification framework.

## (D) Cross-section consistency failures

No additional inconsistency was confirmed in the inspected new endpoints.
The following distinctions were checked against the actual result types.

- The manuscript K polynomial, named variables and ordered children are
  retained. Plain acceptance and the stored-word carrier are compared by
  literal-identity graph morphisms and constructor-preserving algebra
  isomorphisms before transporting initiality.
- Syntax folds target arbitrary actual families over P. Their operations
  need only T-proved support and totality. Constructor commutation is proved;
  the root equations for an arbitrary candidate are extracted from its actual
  algebra-Hom equation. Internal node-count induction proves equality among
  those morphisms, and joint faithfulness yields T-provable graph equality.
- Predicate-slice, base and actual TotalSplit initiality and every-parameter
  stability are constructed. No evaluator, recursive-solution or desired
  initiality conclusion is supplied as an input field.
- The actual standard parser's primitive-recursive certificate is separate
  from the all-PA-model graph/conservation laws. Arbitrary Sigma-one
  coefficient membership is not asserted decidable or primitive recursive.
- Lemma 5.8 uses the original pullback `R_n ×_(F^n) Z^n`. Each child has its
  own conclusion, matched to its prescribed premise; the parent conclusion
  comes from q_n. Nullary rules require no global F point. Model proofs retain
  terminal-fiber points and do not assume all interpreted terminal fibers
  are singletons.
- The derivation universal property is obtained from the constructed ordinary
  tree initiality, actual validator, proved success comparison and proved
  algebra adjunction. The raw carrier keeps only a tree code; validation and
  conclusion values remain existential. Its algebra isomorphism preserves
  the tree inclusion and conclusion, including in TotalSplit.
- The sentence chart is the formula-coordinate image of the actual monic
  sentence inclusion. A chosen pullback carrier need not have the formula's
  code as its raw code. The separate FV=0 identification remains a 5.7
  numerical comparison, not an assumed identity in the image/range proof.
- External finite named syntax and semantic structure K are separated from
  the arithmetic code model. The encoder and semantic lemmas concern standard
  finite trees and N. They do not identify arbitrary nonstandard-length words
  with external finite trees. Validity-negation disjointness uses nonempty K.
- Fixed standard parameter-free B_T presentations do not establish arbitrary
  C(M) operations with nonstandard indices or model parameters. Standard
  extensional equalities are not used as substitutes for PA graph equations.
  External consistency of Gamma is not a PA proof of its consistency.
- The proof-search lift remains partial. The arithmetic application still
  requires the categorical comparison at the interpreted source idempotents.

## (E) Acceptance conditions, non-negotiable

1. Pass the combined build, retained and v46 statement audits, strict source
   checks, and transitive axiom coverage of every new production declaration.
   Keep the permitted axiom set and retained audited declarations unchanged.
2. Compare all tested inputs with committed bytes; confirm the ordinary main
   push and remote ref, then check the Downloads copies byte for byte.
3. Keep 5.1 open until its primitive-recursive trace and uniform graph/index
   requirements are proved, independently of completed object coding.
4. Keep 5.7 and the numerical formula/sentence identifications explicit until
   the actual algorithms, PA equations and fold/free-for comparisons pass.
5. Claim 6.5–6.6 only after the standard-code comparisons and actual coded
   validity factorization/disjointness are proved; then instantiate 6.9.
6. Complete the Gamma predicates, diagonal bounds, partial lift and categorical
   comparison before claiming the arithmetic application. Later indexed,
   numerical, Miller and cosheaf obligations remain separate.

## (F) Not checked / uncertainty log

This review does not cover novelty, the whole manuscript, independent kernel
replay, registry verification or PDF layout. Ignored drafts are not counted
as completed proofs. The full integration audit passed; its source/axiom/commit evidence is recorded
in the accompanying verification JSON.

The strongest confirmed gaps to full v46 completion are the exact computation
bridge, numerical named-variable realization and coded soundness/arithmetic
application. No false manuscript assertion or required manuscript repair was
confirmed. The completed 5.5 and 5.8 proofs resolve the independent review's
principal universal-property objections; they do not by themselves certify
the remaining manuscript. Recommendation for complete v46 formalization:
**unknown** until the stated remaining obligations are discharged.
