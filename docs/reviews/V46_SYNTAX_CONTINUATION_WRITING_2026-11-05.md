# Writing review of the syntax and derivation continuation notes

Scope: the changed correspondence rows, new mathematical module descriptions
and existing implementation/review records for the continuation from
`3f53b33`. Manuscript v46 and its PDF are unchanged. This is a scoped review
of the changed notes, not a whole-paper editorial review.

The governing source consulted in this conversation was Knuth, Larrabee and
Roberts, [*Mathematical Writing*, Stanford report CS-TR-89-1193](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf),
§1 and the definition-placement discussions in §§4–5. The applications below
concern self-contained mathematical statements, definitions before use and
consistent notation. The review format follows the mathematical-writing
skill; it is not attributed to the Stanford report.

The manuscript's existing order is retained: categorical preliminaries and
diagonal comparison; interpreted theories; syntactic recursion categories and
internal syntax; model interpretation; arithmetic; Miller sequences; the
three-point application; Appendices A–D and bibliography. The changed notes
follow the local proof dependency order: actual syntax universal property,
plain/standard parser comparison, arbitrary-rule derivations, sentence-image
charts, then the remaining numerical and semantic realizations. No manuscript
outline or prose revision is made.

| Anchor | Difficulty | Principle applied and repair |
| --- | --- | --- |
| Proposition 5.5 and the new initiality modules | Unique evaluator output could be confused with uniqueness among algebra morphisms. | Self-contained claims and explicit categorical types: name constructor commutation, the arbitrary-Hom uniqueness theorem, every-parameter IsInitial and the actual TotalSplit instance. The completed universal property is stated separately from the evaluator's unique output. |
| Plain-parser acceptance and standard certificate | A changed carrier or a standard-model equation could conceal a missing comparison. | Define the two acceptance predicates and their literal-identity maps; state the constructor-preserving algebra isomorphism. Distinguish PA/T-provable all-model equations from the separate Nat.Primrec certificate. |
| Lemma 5.8 and its rule pullbacks | A single shared formula fiber would change the inference signature. | Explicit types: retain R_n ×_(F^n) Z^n, match each child to its own prescribed premise and obtain the parent conclusion from q_n. Include n=0 and arbitrary coefficient objects. |
| Derivation success carrier | Validation values or computation witnesses could be mistaken for extra syntax labels. | Definition before use: the carrier is a predicate on the original tree code; validation and conclusion values are existential. Its comparison with the chosen pullback preserves the tree and conclusion maps and the algebra structure. |
| Sentence images and literal program ranges | Chosen pullback codes need not be formula codes. | Define the formula-coordinate image chart before calling its predicate Sent. State Th using the actual program graph. Retain the pending identification with numerical Fm and FV=0 at the point of use. |
| Lemma 5.1 status | Object coding, existential trace comparison and uniform parameter/composition properties have different endpoints. | Consistent status terminology: name the completed exponential/parity translations, uniform functionality/universal equation, stage totality and Sigma-one trace/output comparison. List the primitive-recursive trace and uniform index equations still required. |
| External named semantics | Standard finite trees could be confused with nonstandard arithmetic codes, or K with the code model. | Explicit scope: literal Nat names and ordered children belong to the standard-tree comparison. K interprets decoded formulas; arithmetic models interpret codes. Keep nonemptiness in the validity-negation lemma and leave the coded factorization pending. |
| Arithmetic application | An imported arithmetic theorem could obscure the missing categorical instance. | State the remaining Gamma predicates, diagonal bounds, partial search lift and interpreted restriction-idempotent comparison. Distinguish external consistency from a PA proof of consistency. |

Namespace abbreviations, coefficient objects, parameters, the original
inference signature and model roles are specified before the notes use them.
Composition direction agrees with the Lean statements. The code comparisons
retain literal binder names; erasure to de Bruijn syntax is not used as
syntax equality. Decidable variable equality does not assert decidable
membership of arbitrary Sigma-one coefficients.

The changed notes were read continuously for hypothesis and completion-status
consistency. The old claims that 5.5 still lacked constructor/Hom/initiality
proofs and that 5.8 still lacked its arbitrary-rule carrier/fold are replaced
by the proved declarations. The 9.1/B.10 tuple-comparison wording is corrected.
The remaining 5.7/5.9 numerical identifications and coded 6.5–7.3 application
proofs stay explicit. Ignored drafts are not reported as proved.

Final integration, transitive axioms, source-commit identity, remote push and
Downloads-copy claims are supplied from the verification record from the completed
integration audit and subsequent committed-byte checks. No new literature, novelty, independent-kernel,
registry, manuscript-compilation or rendered-page claim is made.
