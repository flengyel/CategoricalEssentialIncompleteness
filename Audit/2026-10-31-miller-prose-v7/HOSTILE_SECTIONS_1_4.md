(A) Kill-shots / hard blockers
================================

**Final v7 disposition.** Checked the actual working v7 source at `manuscript/essential_incompleteness_via_local_connectedness_v7.tex`: C4 is resolved by the precise reference to Miller's stronger index property. Both numerical applications now explicitly use finite derivation trees with sentence conclusions, read their root conclusions, and cite the initial-algebra/pullback characterization. No confirmed mathematical blocker remains from this review. The entries below preserve the historical v6 findings and proposed editorial changes; they should not be read as outstanding objections to v7. The separate final-source audit of the new universal properties is in `tmp/proof_object_initial_audit.md`. Compilation and visual inspection were performed by the coordinating agent, not independently repeated in this audit; no Lean verification is claimed.

None confirmed in the abstract and Sections 1–4 of `output/pdf/essential_incompleteness_via_local_connectedness_v6.tex` (source lines 23–902). This is an author-side mathematical and editorial audit. It is not a journal review and makes no novelty judgment.

The main proofs withstand the following checks. Restriction, totality, partial monicity, range, splitting, and the Turing equation have compatible types. The local-switch proof treats arbitrary partial test arrows by splitting their common composite domain; it does not stop at total arrows. The range-functor proof performs its product calculation entirely in the source before applying F, so it does not secretly assume product preservation. The Miller category requires common domains as well as outputs. Its evaluator is implemented by compactness, not postulated from an external universal quantifier. The cut reduction keeps exact-output unanimity separate from parity. The field-theory result concludes essential incompleteness relative to the stated semidecidability class and makes no claim about completions computable from an individual name.

(B) Major weaknesses
====================

No confirmed major defect in this scope. In particular, there is no evidence warranting deletion or reconstruction of the Miller application.

The two mathematical-language ambiguities below are local and repairable. Neither invalidates the construction once the explicitly described correction is made. The other proposals are reductions of repetition or vague phrasing, not mathematical objections.

Revision status: the working v7 at `manuscript/essential_incompleteness_via_local_connectedness_v7.tex` was inspected after the initial findings. It already repairs C1 (sentence conclusions), C2 (separate searches for exact outputs), and C5 (a concrete presentation of the splitting). Those entries document repaired v6 findings and are not outstanding objections to that working version.

(C) Minor issues
================

1. Proof-object codomain needs one explicit restriction.

- Anchor: Section 4.3, proof of `thm:miller-incompleteness`, source lines 872–881: “let Prf_T be the set of finite derivations” followed by “reading the last sentence gives a total arrow c_T:Prf_T→S.”
- Claim as written: every such derivation has a sentence as its final formula.
- Failure mode: `ambiguous` / local potential `ill_typed`.
- Why: an ordinary first-order calculus can have derivations ending in formulas with free variables; S was defined to contain sentence codes. The manuscript has not restricted the derivations at this point.
- Evidence: `structural_argument`. For example, a usual calculus can derive x=x, which is not a sentence. The map taking the final formula would then miss S.
- Concrete repair: “For a theory T with an E_a-semidecidable axiom set, let Prf_T be the set of finite derivations whose last formula is a sentence, in a fixed recursive first-order calculus.” This adds a recursive syntactic test and leaves the semidecidability argument unchanged.
- Impact: repairs the displayed conclusion arrow and its range. Severity: minor; locally repairable.

2. State that the evaluator runs a separate search for each output.

- Anchor: Section 4.1, proof of `lem:miller-unanimity`, source lines 630–637: “Dovetailing over m, enumerate these cylinders together with those enumerating ... and search for a finite subfamily covering Cantor space.”
- Claim as written: an interleaved enumeration detects the exact-output unanimity condition.
- Failure mode: `ambiguous`.
- Why: the wording can be read as pooling the halting cylinders for different m into one cover. Such a pooled cover tests that every name halts, not that all names return the same number. The next sentence states the correct fixed-m test, so the intended argument is recoverable from the page, but the algorithmic instruction itself should be exact.
- Evidence: `derivation`. Two disjoint nonempty oracle cylinders returning 0 and 1 can together cover the fibre without unanimity.
- Concrete repair: “For each m, search for a finite cover of Cantor space by cylinders enumerated in H_{e,n,m} together with cylinders enumerated in the complement of P_z. Run these searches in parallel over m, and return m when its search succeeds.”
- Impact: prevents an incorrect implementation of the central evaluator. Severity: minor exposition; locally repairable.

3. Make both preimage searches explicitly dovetailed.

- Anchor: Section 4.1, proof of `prop:miller-category`, lines 659–661: “search over the coded inputs x for a computation f(x)=y”; lines 674–675 refer back to “the same preimage search.”
- Failure mode: `ambiguous` at the level of an algorithmic instruction.
- Why: sequentially waiting for f(x) at one input can prevent discovery of a later preimage. Ordinary computability readers will supply the dovetailing, but one word removes this burden.
- Evidence: `derivation`: a partial function undefined at the first enumerated input but attaining y at the second defeats sequential search.
- Concrete repair: “To compute the range partial identity at y, dovetail the computations f(x) over all coded inputs x and return y when one returns y.” The inverse construction may then keep “the same preimage search.”
- Impact: clarity of the effective range and inverse constructions. Severity: minor; locally repairable.

4. The description of the stronger Miller property has a wrong or unclear grammatical object.

- Anchor: Section 1.1, lines 171–172: “The stronger equality between a program index and the corresponding sequence coordinate ...”.
- Failure mode: `ambiguous`.
- Why: the equality is a(d)=r, between a coordinate value and the computed real; it is not an equality of a natural-number index with a coordinate value. The subsequent formal statement is correct.
- Evidence: `derivation` from the displayed property `eq:miller-property`.
- Concrete repair: “The paragraph following that theorem gives the stronger property that a program computing the same real from every representation computes the value of the sequence at its own index.” Alternatively, defer the detail: “We use the stronger index property stated immediately after that theorem and recalled in Section 4.”
- Impact: source attribution and conceptual clarity. Severity: minor; locally repairable.

5. A concrete presentation of the restriction splitting should be named as such.

- Anchor: Section 4.1, lines 703–705: “Concretely, K_p has p-c.e. subsets ... as objects.”
- Failure mode: `ambiguous` (presentation versus literal object equality).
- Why: Section 2 defines split objects as pairs (X,e). The concrete carrier is e's domain; formally different pairs may yield the same displayed subset.
- Evidence: `structural_argument` comparing the declared object descriptions.
- Concrete repair: “We may present K_p concretely by p-c.e. subsets of the numerical objects, with partial p-recursive functions between these carriers.”
- Impact: removes an avoidable change in the meaning of object equality. Severity: minor; no theorem depends on the literal equality of the presentations.

Editorial compression proposals (no mathematical failure asserted)
-----------------------------------------------------------------

The technical sections of Heller's paper are the useful model here: define the data, state the conclusion, and put the calculation immediately after it. His introduction also contains rhetoric; the request to remove empty language does not require copying that rhetoric. The following proposals preserve mathematical content rather than replacing it with terse slogans.

| Anchor | Reason | Concrete replacement or deletion |
|---|---|---|
| Abstract, lines 32–39 | “The same pair” has two plausible antecedents: the diagonal pair and the cut pair. | “The cut pair gives essential incompleteness, relative to computation independent of the name, for the theory of real closed fields with constants specifying the sequence's rational cuts.” |
| Introduction, lines 53–60 | “The essential additional condition” and “Once this condition holds” split a single mathematical assertion into an announcement and a conclusion. | “A Turing morphism gives an inseparable pair in the source when the sections associated with complementary source domains lift through the functor.” Retain the following paragraph's explicit target hypotheses. |
| Introduction, lines 89–90 | “even such functors” is evaluative and makes the reader recover the precise functor class. | “A faithful range functor preserving products can therefore send an inseparable pair to a separable one.” |
| Introduction, lines 92–101 | The last three sentences repeat “relate/relation” without specifying the needed inequalities. | After the incompleteness assertion, use: “The sentences c_n<1/2 pull the theorem and refutation domains back to supersets of L_a and R_a, so Corollary [domain-incompleteness] applies.” |
| Introduction, lines 103–109 | Failure of local connectedness is stated twice in six lines. | Keep the precise sentence ending with DPM Corollary 4.4; change the opening to “We also apply the criterion to the syntactic recursion categories of Montagna and Di Paola–Montagna.” |
| Introduction, lines 115–118 | “place its two sets in the inverse images” is indirect. | “Finite computation proofs show that the two sets lie in the inverse images of the theorem and refutation sets of PA under numeral substitution.” |
| Section 2 opening, lines 181–182 | Repeats the framework stated in the introduction and immediately defined in the subsection. | Delete these two lines and begin with the composition convention. |
| Section 2.1, lines 199–200 | Two sentences for one definition. | “The arrows bar(f) are idempotent and are called restriction idempotents.” |
| Section 2.2, lines 282–283 | “covariant” adds no distinction; every functor in this discussion is covariant unless marked otherwise. | “A range functor F:C→D preserves restrictions, ranges, restriction zeros, and binary restriction coproducts.” |
| Section 3 opening, lines 336–343 | Repeats the introduction and then announces again that the following argument supplies sections. | Delete “The following argument supplies the needed sections.” The three-sentence section opening can also be reduced to “Local connectedness supplies the sections used in the following lifting criterion.” |
| Theorem `thm:local-lifting`, line 427 | “prodominical recursion category” repeats a property already built into the definition at lines 330–332. | “Let R be a recursion category with ranges and binary restriction coproducts.” |
| Section 3.3, lines 512–515 | Four lines announce that the next corollary states a connection; the statement gives the connection explicitly. | “The next corollary transfers inseparability to theorem and refutation domains.” Or delete the paragraph if the subsection title is retained. |
| Section 4 opening, lines 564–568 | Repeats the introduction's detailed summary before the construction begins. | Delete the paragraph and begin “Fix a recursive bijection ...”. The section title and subsections already supply orientation. |
| Proposition `prop:miller-category`, lines 662–664 | “This proves range closure” names a proof step rather than its result. | “Thus ran(f) belongs to E_a; its leastness and agreement law follow from those of set-theoretic images.” |
| Section 4.2, lines 739–740 | “We next reduce ...” repeats the immediately following lemma. | Delete the sentence; retain the semidecidability justification before it. |
| After the cut corollary, lines 828–832 | The final clause repeats the first sentence. | Keep the first two sentences and end “The category Rec^p has its own Turing morphism.” |
| Field-theory proof, lines 893–895 | “makes these two source domains inseparable” suggests the corollary performs an operation. | “By Corollary [cuts], the two source domains are inseparable; the full inclusion into the restriction splitting preserves this property.” |

Do not remove the sentences distinguishing common numerical values from possibly different rational names, simultaneous undefinedness, the exceptional case a(n)=1/2, the empty bad-box case, or the relative semidecidability condition. Those qualifications carry mathematical content.

(D) Cross-section consistency failures
====================================

No mathematical inconsistency was found within Sections 1–4. The presentation issue in C5 and the misleading wording in C4 are the only local definition/description mismatches found.

Checked dependency and typing inventory:

- Section 2 supplies the restriction order, compatibility, joins, inverse images, ranges, split objects, products, coproducts, range functors, local connectedness, weak choice, and Turing equation before their technical use.
- The inverse-image assumption in the connected-alternative lemma applies to partial arrows as well as total ones; applying it to a restriction idempotent justifies distributing the meet with a over the displayed join. No unstated lattice distributivity is needed.
- The local-switch proof uses splitness only to pass from arbitrary partial u,v to total maps on their common composite domain. It uses local connectedness to detect equality and weak choice to obtain the inverse section. The uniqueness calculation has the right types.
- In the lifting theorem, u:U⇀U and g:U→U; precomposition with ⟨1_U,g⟩ is legitimate because g is total. E=Fg is total without F preserving products. Both target pullback inequalities have the correct orientation.
- In the domain-incompleteness corollary, the pullback is along total theta, exactly matching the weaker join-preservation hypothesis stated there. No involution condition on nu is used or needed for the abstract corollary.
- E_a has formal numerical objects generated only by binary products and sums; its isotypical claim is therefore compatible with the later use of splitting to obtain sentence and proof objects. E_a itself is not silently declared split.
- The functors J_p and I_p preserve the structures required by the criterion; product preservation is asserted only where available. The particular image evaluator need not be universal, and the manuscript correctly demonstrates that it is not.
- The cut reduction's scalar r_e remains in [1/4,3/4], within the interval of the strong Miller property. The first-digit separator has the correct orientation relative to L_a and R_a.
- The field-theory proof needs only the two half-cut instances of the full rational-cut axioms. This is a valid use of a stronger base theory, not an inconsistency or an unproved generalization.

(E) Acceptance conditions, non-negotiable
=======================================

For the requested sentence-level revision, the following endpoints are concrete and sufficient within this scope:

1. Define Prf_T to contain derivations ending in sentences, so the displayed c_T has its stated codomain. Failure leaves a local typing ambiguity; no central claim need be dropped if the sentence is repaired.
2. Specify one finite-cover search per numerical output m and dovetail those searches. Failure leaves an avoidable ambiguity in the central algorithm; a pooled-output interpretation must not be used.
3. Replace the prose description “equality between a program index and ... coordinate” by a statement of the actual index property or a direct reference to its displayed equation. Failure leaves an inaccurate explanation, not a false formal theorem.
4. Remove the repeated announcements identified above while retaining all proof-bearing qualifications. Endpoint: the revised Sections 1–4 state each definition, hypothesis, and transition once where it is needed. This is an editorial requirement of the user's request, not grounds for mathematical rejection.

No additional theorem, example, hypothesis, approval step, or formalization is demanded by this report. The optional concrete-presentation and dovetail-wording repairs can be made in the same pass.

(F) Not checked / uncertainty log
================================

Every sentence from the abstract through the end of Section 4 was read in the actual v6 TeX source. The mathematical review included all definitions, all displayed claims, and the proofs in this interval. The review also used the relevant technical sections of the supplied Heller 1990 text, especially Sections 5–6 and 8–9. Its OCR is imperfect, so no typographical feature of that extraction is offered as an authorial model.

The primary Miller and Bauer–Hanson source dependencies were independently checked in the preceding v6 audit; the current source retains those statements unchanged. The fixed-point existence proof was not reconstructed anew. Historical priority claims about Bernardi, Montagna, Di Paola–Heller, and the precise Cockett–Lack proposition were not freshly source-audited in this narrower pass; no new contrary evidence was found. Sections 5 onward, bibliography accuracy, rendered pages, compilation, repository state, and Lean are outside this assigned scope.

Strongest confirmed blocker: none. Strongest confirmed local defect in v6: Prf_T was not explicitly restricted to derivations with a sentence conclusion; the inspected working v7 repairs it. The remaining precise prose correction is the description of Miller's index property in C4. Strongest suspected unconfirmed blocker: none identified. Most important thing not checked in this pass: the external fixed-point existence proof and the later retained applications. A whole-paper recommendation would require those separate reviews. Final recommendation under the requested hostile-audit schema: **unknown**; this is not a rejection recommendation, and no major reconstruction of Sections 1–4 is supported by the evidence.
