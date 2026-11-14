# Audit of §9, §10, Appendix B, and Appendix C — v57

Source revision: `dfe6d3b9b948875d9d268ef8bbd332d65c6b53e5`. This is an author-side mathematical audit, not an external peer-review report. All 28 numbered proofs in the assigned scope were read and reconstructed. The companion `examples-ledger.json` records the hypotheses, dependencies, and derivation for each result.

## Functional outline and dependencies

The manuscript's literal heading order agrees with the functional structure below. Appendix B is read before §10 for dependency checking, although it remains supplementary to the main exposition.

| Unit | Mathematical function | Inputs | Output used later |
|---|---|---|---|
| §9.1–9.2 | Construct computation independent of a binary representation | Compact fibers of the binary representation map; oracle parameter theorem | Recursion category `E_a`, its Turing morphism, ranges, conditionals, and an inseparable diagonal pair |
| §9.3–9.4 | Replace program indices by cuts in a Miller sequence | Effective finite cylinder covers; Miller's fixed-index property | A total recursive reduction from the diagonal pair to the sets below and above `1/2` |
| §9.5–9.6 | Construct internal first-order deduction | Numerical coding; common domains and values of representing programs | Regular/extensive total category, partial inverses, parameterized syntax and finite derivations |
| §9.7–9.8 | Apply the general incompleteness and associated-category theorems | Cut reduction; consistent field theory; §9.5–9.6 | Essential incompleteness, inseparability, and the slice-category instance |
| Appendix B.1–B.4 | Construct the ambient partial-map category | The fork `1 ← 0 → 2`; c.e. numerical carriers | Cosheaf comparison, regular/extensive total category, ranges, local connectedness |
| Appendix B.5–B.8 | Construct the recursion category | Explicit embeddings, frames, and synchronized component programs | A Turing object and restriction-splitting equivalence |
| Appendix B.9–B.10 | Compare completions and distinguish the model | Image splittings; terminal subobjects; naturality | Karoubi equivalence; non-equivalence to partial recursive functions; failure of decidable equality on `V` |
| §10.1–10.6 | Transfer an inseparable pair to propositional deduction and endpoint theories | Appendix B; finite formula and derivation trees | Consistent internally essentially incomplete theory and two externally essentially incomplete c.e. theories |
| §10.7–10.9 | Add first-order syntax conservatively, then apply §5 | Constant variable object; equality erasure; parameterized deduction | Conservative first-order theory and associated Turing-category instance |
| Appendix C.1 | Exhibit the necessity of the lifting hypothesis | K-c.e. domains with ordinary partial recursive extensions | A faithful range functor whose target separator has no source lift |

The three-point construction uses endpoint Turing morphisms only at components 1 and 2. The manuscript explicitly disproves the corresponding claim at component 0; no reviewed later proof silently uses that false extension.

## (A) Kill-shots / hard blockers

None confirmed in the assigned scope. Every assigned theorem statement has a reconstructible derivation from its printed hypotheses and the cited general results. This verdict does not substitute for the separate audit of those general results or for Lean statement comparison.

## (B) Major weaknesses

None confirmed in the assigned scope. The following points received explicit adversarial checks:

- **Uniform oracle quantifiers.** Lemma 9.1 searches for one value `m` produced by every representation in the compact fiber. It does not confuse a possibly representation-dependent answer with a common partial function. Its finite-cover test has the required uniformity in the supplied representation.
- **Miller reduction.** Lemma 9.3 first constructs a uniformly computable real-valued function on the whole Hilbert cube, then obtains a total recursive program-index map by specialization. The Miller property is applied to that index. The disjointness of the two open sets makes the sign of the difference of the two nonnegative sums correct.
- **Descent and weak choice.** Proposition 9.5 permits a search witness to vary with the oracle but requires its descended value to be fixed by the kernel-pair condition. Preimage search for a monomorphism is safe because the preimage itself is unique. Neither proof selects a representation-dependent value as a morphism.
- **Domain equality in the three-point Turing morphism.** In Theorem B.7, the central component runs its own specialized program and both endpoint programs. The subfunctor and naturality conditions ensure that every point of the prescribed central domain passes the checks. Conversely, halting of its own program forces membership in the prescribed domain. The proof establishes both inclusions, not only agreement where both sides happen to be defined.
- **Conservativity.** Proposition 10.8 erases quantification and sends equality to a fixed propositional theorem. This is valid for its language because terms are variables and predicates are nullary. Its substitution identity would require additional arguments in a larger language; the proposition does not claim that extension.
- **Associated-category hypotheses.** Corollaries 9.8 and 10.9 cite explicit parameterized syntax/derivation results (9.6 and 10.7), regularity and partial inverses, a total reduction of an inseparable pair, and a global logical theorem. They therefore instantiate the printed hypotheses of Theorems 5.2 and 5.3 rather than replacing them with an unproved assertion that the examples have the right form.

## (C) Minor issues

**B.10: equality uses opposite truth-summand conventions in the two appendices.** Anchor: Appendix B, p. 80, `appendices/b-three-point-cosheaves.tex:568–570`, defines decidable equality by saying that “the first summand is the diagonal subfunctor”; line 594 repeats “first summand” in the proof of Proposition B.10 (`prop:fork-distinction`). Appendix A, p. 67, `appendices/a-syntax-and-theories.tex:37–38`, orders the injections as `f,t`, and p. 67, lines 130–142, defines equality by pulling back `t`, the second injection. Failure mode: `inconsistent_use`. Evidence label: `derivation`; the two displayed definitions select different named truth values. Severity: **minor**. Repairability: replace both Appendix B occurrences of “first” by “second,” consistently with Appendix A. The nonexistence proof is unchanged: naturality forces the decision on distinct central tuples to equal the decision on their equal endpoint images, regardless of which summand represents truth. No theorem-level blocker follows.

No terminology replacement is recommended merely because a term sounds computational: “oracle program,” “program index,” “finite tree,” and “domain of definition” designate precisely specified objects in these proofs.

The KLR manual was inspected only through its table of contents and opening technical-writing guidance during this assignment. The complete manual was not read by this reviewer. No claim of a complete KLR writing audit is made here; the dedicated writing review covers that task.

## (D) Cross-section consistency failures

The equality convention mismatch recorded in (C) is a confirmed cross-section inconsistency. It does not change Proposition B.10 or any downstream conclusion after the two local wording corrections. The principal interfaces were checked as follows.

| Interface | Check |
|---|---|
| §9.2 → §3.3 | The inclusion into the split p-recursive category is a range functor, has nonzero Turing-object identity, preserves the required joins, and receives total source conditionals. |
| §9.4 → §9.7 | The cut sets have common oracle-semidecision procedures, and the recursive map `theta(n)` is defined on all natural numbers. The positive and negative inequalities have the stated orientation. |
| §9.5–9.6 → §5 | Every monomorphism has a partial inverse, and finite derivations exist for axiom subobjects over arbitrary parameters, including nullary languages with labels in an arbitrary object. |
| Appendix B → §10.1 | Endpoint evaluation preserves the partial-map operations; the endpoint parameterization works for every c.e. parameter carrier. No claim is made that arbitrary central-component programs lift to natural transformations. |
| §10.4 → §10.5 | The theorem carrier is the componentwise image of the initial derivation algebra, so applying endpoint evaluation really gives the c.e. theorem and refutation sets used in the argument. |
| §10.6 → §10.8 | Enlarging one endpoint theory preserves fork compatibility because the central theory is unchanged and its image was already included in that endpoint. The propositional restriction of a complete first-order theory is complete because the embedding preserves negation. |
| §10.7–10.8 → §10.9 | The global propositional theorem maps into the first-order sentence object, giving the required section; the source inseparable pair remains the pair reduced by the first-order atom constructor. |
| Appendix C → §3 | Finite joins of restriction idempotents do not imply joins of arbitrary disjoint partial morphisms. The example supplies the former and disproves the latter, so it does not contradict Proposition 3.4. |

## (E) Acceptance conditions, non-negotiable

1. Retain the exact common-domain/common-value oracle condition in §9; replacing it with a statement that each representation computes some separator would invalidate the inseparability argument.
2. Retain both central-domain inclusions in Theorem B.7 and the distinction between endpoint and central evaluation in §10. Failure of either requirement invalidates the claimed recursion-category realization.
3. Retain the parameterized deduction hypotheses and the global logical theorem in Corollaries 9.8 and 10.9. Without them the associated-category claims are not established by the general theorem.
4. Before an overall acceptance judgment, integrate the independent audit of Theorems 3.1–5.3 and Appendix A. A failure there propagates to the examples despite the locally correct specializations.

5. Harmonize the two truth-summand references in Proposition B.10 with Appendix A and verify both occurrences. This is a local notation correction; failure to make it does not refute the nonexistence theorem, but leaves the manuscript internally inconsistent.

No additional mathematical repair is presently demanded by the assigned scope.

## (F) Not checked / uncertainty log

- No Lean declaration or axiom audit was performed by this reviewer.
- The original Miller 2004 paper was not independently read. The stated fixed-index property was checked against the primary source Bauer–Hanson, *The countable reals*, arXiv:2404.01256v3, Definition 2.1 and Theorem 2.2, which uses exactly the uniform representation quantifier and fixed program index required here. Source: https://arxiv.org/html/2404.01256v3, Definition 2.1 and Theorem 2.2.
- No independent priority or novelty search was performed. None of the local verdicts establishes novelty.
- The ambient general theorems were read to check the application interfaces, but their separate full audit belongs to the assigned general-theorem reviewers.
- The categorical realization is checked in the displayed set-theoretic/c.e. models. No mechanized verification of the tuple or tree encodings was undertaken.

Strongest confirmed blocker: none in the assigned scope; the strongest confirmed defect is the minor truth-summand convention mismatch in Proposition B.10. Strongest suspected unconfirmed blocker: none presently identified; correctness still depends on the general theorem and syntax audits. Most important unchecked item: exact Lean correspondence for the 28 reviewed results and their dependencies. The local mathematical judgment does not depend on unavailable text, except that the original Miller attribution was checked through the cited Bauer–Hanson formulation. Final overall recommendation: **unknown**, because this is a scoped audit; the assigned mathematical material supports proceeding subject to the remaining audits and the local convention correction.
