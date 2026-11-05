# Writing review of the syntax continuation notes

Scope: changed correspondence rows, new module descriptions and the existing
implementation/review records after `4cde20bb86ed`. Manuscript v46, its TeX
and PDF are unchanged. This is a scoped notes review, not a whole-manuscript
editorial review.

The governing source already consulted in this conversation is Knuth,
Larrabee and Roberts, [*Mathematical Writing*, Stanford CS-TR-89-1193](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf),
§1 and the definition-placement discussions in §§4–5. The applications here
concern self-contained claims, definitions before use and consistent model
roles. The review format follows the mathematical-writing skill and is not
attributed to the Stanford report.

| Anchor | Difficulty | Applied repair |
| --- | --- | --- |
| Retained 5.5/5.8 initiality | Evaluator uniqueness could be confused with uniqueness among algebra morphisms, or arbitrary rules with a particular calculus. | Name actual Hom equations, every-parameter initiality, original typed premise pullbacks, nullary rules and the TotalSplit endpoints. |
| Numerical versus categorical operations | PA numerical algorithms and arbitrary T-total algebra operations have different proof obligations. | State their proofs separately. Name the actual occurrence Hom and initiality comparison; retain substitution/Adm and TotalSplit transport as open. |
| Standard named comparison | Finite trees might be confused with nonstandard words, or binder erasure with syntax equality. | Specify N, literal names, labels, repetitions and ordered children; keep all-model graph equations separate. |
| Sentence predicate and generated theory | A chosen pullback code might be taken as a formula code, or a structural image theorem as the whole numerical realization. | Define the formula-coordinate image first. State its proved plain Fm and FV=0 comparison, the constructed closure/leastness and the remaining operation identifications separately. |
| Trace comparison | Completed object coding, a primitive-recursive Tr predicate and uniform index equations might be merged into one completion claim. | Mark the first two complete and list exactly uniform comp/s, total parameter-index programs and production graph/index comparison as remaining. |
| Semantic application | Individual schemes or induction resources could be mistaken for soundness of the actual proof object. | Name the four actual coded schemes and two rules proved, then retain the three remaining schemes and unique sentence validity factor. Keep semantic K distinct from arithmetic M/N. |
| Arithmetic application | An imported incompleteness theorem could conceal the categorical instance. | Retain the actual Gamma predicates, diagonal bounds, partial search lift, categorical comparison and exact model scope. External consistency is not a PA proof of consistency. |

The changed notes follow the existing dependency order and define namespace
abbreviations, coefficient objects, parameters and model roles before use.
Completion status is stated at the same point as the relevant claim. The
independent review's source/evidence-only scope is explicit, including that
it did not independently rerun Lean or establish v46 completion.

Rows 9.1/B.10 retain the corrected tuple-comparison wording. No manuscript
prose revision, new literature claim, registry claim, independent-kernel
claim or rendered-page claim is made. Ignored drafts are not reported as
proved. The failed import placement and its minimal repair are stated in
the implementation/review record without treating them as a mathematical
error or changing the theorem statements.

Final verification, permitted axioms, tested-source identity, ordinary push
and committed-byte delivery are recorded from the completed checks, not
inferred from declaration counts or a source-only review.
