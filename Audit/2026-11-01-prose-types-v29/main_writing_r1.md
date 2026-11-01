# Mathematical-writing review of the version 28 revision

The changed arguments are readable and preserve the distinction between source conditionals and arbitrary target separators. Three passages need local clarification: Proposition C.1 does not identify its pair in the statement, the introduction's roadmap names the wrong locations, and Appendix D still describes a source hypothesis through interpreted target conditionals. The new proof of Corollary 3.3 and the inverse-copairing construction in Section 9.1 do not need compression.

## Source and scope

Manuscript: *Logical consequence and essential incompleteness in recursion categories*, version 28, 1 November 2026. Reviewed `tmp/move28/main.diff` and all changed mathematical passages in their current source context: abstract; introduction; Section 3; the model corollary in Section 6; the final attribution in Section 7; Section 7.5; the conditional constructions and comparison applications in Section 8; Section 9.1 and the endpoint application in Section 9.4; Appendices C and D. Supporting definitions were read in Section 2. This is a review of the revision, not an independent review of the unchanged 77-page paper.

Governing source consulted: Knuth, Larrabee, and Roberts, *Mathematical Writing*, Stanford report, local supplied copy `tmp/review_sources/klr.pdf` and extracted `klr.txt`: Section 1, printed pp. 1–5, particularly points 5, 10–17, and 26; Sections 4–5, printed pp. 9–13. Section 1 recommends self-contained theorem statements, definitions when variables first occur, connected exposition, and consistent notation. Sections 4–5 permit appropriate postponement of part of a definition and warn against carrying that postponement too far. The report format and the terminology preferences below are editorial choices, not prescriptions attributed to the report.

## Actual outline and dependencies of the revised material

| Location | Mathematical function and dependency |
|---|---|
| Abstract and introduction | Preview the comparison theorem and its applications; distinguish a lifted target conditional from a total conditional constructed in the source. |
| Section 3.1, Theorem 3.1 and Corollary 3.2 | A Turing morphism and a lift of a target conditional yield a total source morphism avoiding both target domains; a nonzero target identity and preservation of the relevant join exclude a target complement. These results are retained. |
| Section 3.2, Corollary 3.3 | Apply Corollary 3.2 to total source conditionals on complementary restriction domains. The proof derives the summand inverse-image equations using the agreement law for ranges. |
| Section 3.2, Proposition 3.4 | Construct those conditionals as joins of two partial morphisms with disjoint restriction idempotents. |
| Section 6, Corollary 6.3 | Apply Corollary 3.3 using the previously proved source search construction and the interpretation functor into partial functions. |
| Section 7.5 | Construct the numerical source conditional by parallel membership search, and apply Corollary 3.3 before the retained arithmetic-domain comparison. |
| Section 8.1 | Give the representation-independent source search construction and apply Corollary 3.3 through the fixed-representation comparison functor. |
| Section 8.2 | Use the fixed-representation separator to show that the comparison functor does not preserve the chosen Turing morphism. |
| Section 9.1 | Prove that a copairing of complementary subfunctor inclusions is an isomorphism; compose its inverse with a tagged copairing to construct the source conditional. |
| Section 9.4 | Apply the same criterion in the full numerical endpoint category. |
| Appendix C | Exhibit a range functor, a complementary target separator and its conditional, and the failure of a source lift. Also exhibit disjoint-domain morphisms without a common upper bound. |
| Appendix D.1 | Apply Corollary 3.3 to the faithful model-family functor and preserve the pair under theory extension. |

No reorganization of the mathematical sections is needed for this revision.

## Findings and concrete repairs

| Anchor | Difficulty | Source principle or editorial rationale | Action |
|---|---|---|---|
| Proposition C.1, p. 72; `appendices/c-section-lifting.tex`, lines 52–54: “For the Turing morphism and coproduct isomorphism constructed below, the specified pair…” | No pair has been specified in the statement. The reader must enter the proof to discover its formula and the intended existential assertion. | KLR Section 1, point 5: a theorem statement should usually be self-contained. | Quantify the Turing morphism and coproduct isomorphism in the statement and display the pair; replacement below. |
| Introduction, p. 2, roadmap; `sections/01-introduction.tex`, lines 80–89 | Section 3 has no incompleteness corollary; that is in Section 4. “Sections 6–D” conflates a section interval with Appendix D. The roadmap also mentions the Miller application before the earlier syntactic and arithmetic sections. | KLR Section 1, points 12–13: explain the reader's next step and make the prose intelligible independently of formulas. The correction of reference order is an independent editorial inference from `main.tex`. | Replace the roadmap with the actual order, keeping Appendix D separate. |
| Corollary D.2 and proof, p. 75; `appendices/d-faithful-family.tex`, lines 96–97 and 111–116 | The “conditional hypothesis” is a condition on total morphisms in the source, but is attributed to the functor. The proof then repeats what the source morphism's image does in each model although Corollary 3.3 only needs that source morphism. This obscures which hypotheses are source conditions and which are target conditions. | KLR Section 1, points 10–11 and 17: connect the inference and distinguish the variables and relations involved. | Start with a quantified theory and state the source morphism with its type and equations in the proof; then state the target hypotheses. |
| Section 9.4, p. 54; `sections/09-three-point-space.tex`, lines 339–342: “their switching sections … The same switching construction…” | The proof now applies the conditional criterion, but retains the prior section terminology. No separate “switching” operation is defined. The intended construction is the conditional already displayed in Section 7.5. | KLR Section 1, point 14: consistent terminology. The preference for “conditional” over “switching section” is an independent editorial judgment, supported by the displayed equations in Corollary 3.3. | Replace by “their conditionals are total recursive morphisms and belong to … by fullness. This is the construction in Section 7.5.” Use the subsection label rather than the whole arithmetic-section label. |
| Corollary 3.3 proof, p. 6; `sections/03-sections-and-inseparability.tex`, line 122: “range agreement” | The defined name in Section 2 is the “agreement law” for ranges. The shorter inversion is understandable but unnecessary. | Independent consistency edit, not a mathematical defect. | Write “the agreement law for ranges gives”. |
| Introduction, p. 1; `sections/01-introduction.tex`, lines 3–6: “establishes recursive inseparability in a recursion category” | Section 2 defines inseparability of restriction idempotents. The adjective “recursive” belongs to the numerical application unless an additional categorical convention is declared. | Independent terminology check against the paper's own definition, not an attribution to KLR. | Write “establishes inseparability of restriction idempotents in a recursion category”. |

The pair specification, roadmap, source/target distinction in Appendix D, and categorical use of “inseparability” are necessary local clarifications. Replacing “switching sections” is a necessary consistency repair for this revised application, but the exact wording is flexible; a typed reference to the already proved Section 7.5 construction is preferable to repeating its numerical search proof. “The agreement law for ranges” is optional terminology polish. None of these findings establishes a false theorem.

### Exact replacement for the pair assertion in Proposition C.1

Replace its sentences beginning “For the Turing morphism…” by:

```latex
There are a Turing morphism
$\tau_K:\N\times\N\rightharpoonup\N$ and an isomorphism
$b:\N\to\N+\N$ for which the restriction idempotents
\[
 a_0=(b\tau_K\Delta_{\N})^*(1_{\N}+0_{\N}),\qquad
 a_1=(b\tau_K\Delta_{\N})^*(0_{\N}+1_{\N})
\]
are separated by complementary restriction idempotents in
$\mathcal C_K$.
```

The existing proof constructs precisely these data. This does not alter the claim or its proof.

### Exact replacement for the introduction's roadmap

```latex
After the preliminaries, Section~\ref{sec:lifting} proves the
comparison theorem and the criterion using source conditionals.
Section~\ref{sec:internal-theories} applies the comparison theorem
to internal theories.
Section~\ref{sec:syntactic} constructs the syntactic recursion category
and its internal syntax and theories, and Section~\ref{sec:models}
constructs the interpretation functors and proves soundness.
Sections~\ref{sec:arithmetic}, \ref{sec:miller}, and~\ref{sec:cosheaves}
give the arithmetic, Miller, and cosheaf applications, respectively.
Appendix~\ref{app:syntax-theories} constructs syntax and deductively
closed theories categorically. The remaining appendices give the
cosheaf construction, the counterexample to inseparability without
section lifting, and the faithful model family and its behavior under
theory extension.
```

This repairs the factual roadmap rather than reopening the reserved substantive revision of the introduction.

### Exact local repair in Appendix D

Begin Corollary D.2 with:

```latex
Let $T\supseteq\PA$ be consistent.
Fix $U=\omega$ and a Turing morphism
```

Replace the first paragraph of its proof, before the theory-extension argument, by:

```latex
By Lemma~\ref{lem:switch}, every complementary pair $c,c'$ on $U$
admits a total morphism $s:U\to U+U$ with
$sc=i_1c$ and $sc'=i_0c'$.
Theorem~\ref{thm:faithful} gives a range functor $F_T$ with
$F_T(1_U)\ne0$, and total inverse images in $\mathcal D_T$ preserve
binary joins coordinatewise. Corollary~\ref{cor:source-conditionals}
therefore applies.
```

The two equations retain the complete source condition; no target-lifting conclusion is being substituted for it.

## Definition order, typing, and terminology

- Composition, restrictions, complementary pairs, inverse images, ranges and their agreement law, restriction coproducts, the comparison isomorphism `chi`, and the Turing property are defined in Section 2 before Section 3. No new definition-order defect was found in the revised corollary.
- Corollary 3.3 types `ell_c:U -> U+U` and both coproduct injections. Its target conditional `s_c:FU -> FU+FU` and the comparison isomorphism have matching types. The equations for inverse images are justified by the preceding restriction calculation; they do not need to be replaced by a shorter assertion.
- In Section 8.1, the inputs are explicitly complementary restriction idempotents in `E_a`. The expanded explanation that both the domain and the tagged output are independent of the representation is necessary for membership in `E_a`; retain it.
- In Section 9.1, the domains, inclusions, copairing, component inverses, naturality equation and final copairing are all typed. The componentwise inverse is proved computable and natural, rather than treating a set-theoretic bijection as an isomorphism automatically. Retain these details.
- “Conditional” is established mathematical and programming terminology and is supported here by the displayed case equations. “Complementary conditionals” is a compact descriptive heading, not an additional mathematical object requiring a new definition. No renaming is necessary merely because the phrase is not itself a standard named theorem.
- “Standard” in “standard codes” and “standard natural numbers” has its model-theoretic meaning. It is not an empty adjective. No occurrences of “genuine,” “actual,” “bona fide,” or a purported “coproduct table” occur in the changed passages.
- The introduction's expression “exchange the coproduct tags” is an informal preview of the two displayed branch equations in Corollary 3.3. The object `U` need not itself be a coproduct. If literal precision is preferred even in this preview, write “select opposite coproduct summands on complementary source domains”; this is optional wording, not a missing mathematical condition.

## Scope and checks not made

The changed source and its needed definitions were read; the actual order was checked against `main.tex` and the numbered result/page anchors against `main.aux`. No source edits were made. No compilation or rendered-page inspection was performed in this agent's task. External literature claims and unchanged proofs were not independently verified. The revised comparison proof was checked for the particular explanatory and typing dependencies discussed above; this report does not certify all mathematics in the paper.
