# Mathematical-writing review

The note now presents the computational and deductive constructions with explicit categorical types. The local repairs identified in this review have been integrated: the abstract preserves the recursive-presentation hypothesis and arity bound, the normalization sentence has the same bound, and the repeated comparison with cofree trees has been consolidated. The general existence problem is stated as a problem rather than as a theorem already proved. No LLM-facing or editorial-process remarks occur in the mathematical text.

**Manuscript:** Florian Lengyel, *Domains, finite proofs, and essential incompleteness*, 29 October 2026. Reviewed the complete assembled LaTeX source, all thirteen sections, bibliography, and the separate outline. The first reviewed PDF has 23 pages. Final-snapshot status is recorded below.

**Governing source:** Donald E. Knuth, Tracy Larrabee, and Paul M. Roberts, *Mathematical Writing*, supplied Library copy. Directly consulted §1, printed pp. 1–6 (PDF pp. 3–8), and §§4–5, printed pp. 9–13 (PDF pp. 11–15), through the supplied text extraction. The report distinguishes that source's advice from the plugin's independent requirements. The invalid local file named `knuth-cs1193.pdf` was not used as evidence.

## Actual outline and dependencies

The central question is how computational inseparability constrains effective deduction through a specified category of assertions and finite proofs.

1. **Computation, assertions, and deduction:** states the problem, identifies the three steps of the incompleteness argument, and locates the constructions in the literature.
2. **Restriction domains and direct images:** defines the restriction and range structures, the contravariant domain functor, direct images, and the local adjunction. These support the subsequent domain calculations.
3. **Hoare assertions as profunctors:** gives the profunctor convention, object and morphism actions, composition, total/partial comparison, and behavior under program extension.
4. **Weakest liberal preconditions and representability:** distinguishes domain representability from the existence of a presheaf. **§4.1** proves the numerical criterion and distinguishes pointwise existence, uniform synthesis, and effective formula construction.
5. **Stable unions of domains:** states Heller's definition and the additional universal range property; proves preservation laws and defines the bounded-distributive-lattice-valued functor.
6. **Categorical separation and proof codes:** defines separation, consistency, and completeness, then proves the witness-square transfer theorem. **§6.1** proves the separate representation-based theorem needed for the arithmetic corollary.
7. **The numerical category and effective unions:** defines the partial-recursive category, realizes ranges, and distinguishes uniformly effective unions from arbitrary increasing families.
8. **A Turing morphism and inseparable domains:** specifies parameter universality and binary case distinction; proves inseparability through the identity `dg = hg`; verifies the numerical instance.
9. **Typed inference rules and polynomial functors:** specifies premise and conclusion types, the functor on families, the monoidal category of polynomials, coactions, and the backward action on premise positions.
10. **Finite proofs in a computational category:** defines the restriction-idempotent splitting and its total category, recursive rule presentations, and the polynomial slice functor; proves the computable finite-proof initial algebra. **§10.1** defines presentation translations and the proof functor. **§10.2** proves the general range-functor proposition and obtains the theorem-object functor.
11. **Profunctors and polynomial bicomodules:** constructs and proves the adjunction induced by a profunctor, its composition law, and its application to Hoare profunctors. The final paragraph distinguishes these functor-category adjoints from domain-valued weakest liberal preconditions.
12. **A numerical deductive construction:** **§12.1** constructs traces, axioms, proof and refutation objects, commuting maps, consistency, and inseparability. **§12.2** defines theories and deductive categories, realizes effective extensions, and proves essential incompleteness. **§12.3** gives the Hoare interpretation. **§12.4** proves the conditional arithmetic corollary with jointly recursive substitution. **§12.5** states an interpretation criterion and compares semantic predicate transformation.
13. **Logical presentations in recursion categories:** states the remaining abstract existence problem, relates it to the monograph's question about coding, and identifies the separate arithmetic interpretation problem.

The dependencies in the separate `OUTLINE.md` agree with the manuscript. The former four appendices are absent; no main result refers to them. The order of sections can be retained. The semantic constructions in §§3–4 and 11 have a stated comparative role and are not presented as hypotheses of the numerical incompleteness theorem.

## Findings and repairs

| Manuscript anchor | Actual difficulty | Source principle or editorial rationale | Recommended action |
|---|---|---|---|
| Abstract, “Finite inference rules determine polynomial functors” | “Finite” can suggest finitely many instances; the numerical theorem assumes recursive presentations and permits infinite instance sets. The recursive hypothesis is also needed in the ensuing initial-algebra clause. | §1 point 5 on statement scope, point 17 on unambiguous reading; preservation of mathematical hypotheses. | Say “Recursive presentations by rules with finitely many premises determine polynomial functors”. Alternatively use the defined term “recursive rule presentations” without expanding the arity. |
| §10, paragraph defining recursive rule presentations, “A c.e. list of rules can be presented in this form” | The definition has only `A_0,A_1,A_2`. The sentence as written does not limit the list's arities, and could assert a normalization of arbitrary rules that has not been given. | §1 point 17; supplementary requirement to preserve quantifiers and scope. | Insert “with at most two premises”. No theorem change is needed. |
| §9, first use of `Sy` and `y^{B_a}` | These polynomial notations are conventional in the cited monograph but have not been explicitly evaluated in the note. The monoidal category is central to the account. | §1 point 11 and §5, printed p. 12, on defining symbols near use; this is audience-sensitive clarification. | Add “Here `y^B(X)=X^B` and `Sy=\coprod_{s\in S}y`.” |
| §10 after Theorem `poly:initial`, and §13 paragraph beginning “Niu and Spivak ask” | The initial/cofree distinction is explained twice. The first version includes the substantive cardinality example; the second repeats it without a new consequence. | Plugin economy requirement; §1 points 10–13 favor connected explanation rather than repeated formulas and assertions. | Retain §10's distinction and cardinality example. In §13 retain the monograph question and refer back to §10 rather than repeating the distinction. |
| §13 opening paragraph | It recounts the complete dependency chain already stated in the introduction and proved in §§8–12. The actual existence problem supplies the section's mathematical purpose. | Plugin prohibition on retrospective proof-audit summaries; §1 point 12 on the next information the reader needs. | Delete the recap and begin with the stated existence problem. |
| Theorem `ct:representation-inseparable`, “Under these hypotheses” | Its assumptions are immediately above it, so the claim is locally readable, but the theorem cannot be quoted by itself without importing the entire preceding paragraph and equation. | §1 point 5 says theorem statements should usually be self-contained; §4 cautions that placement is contextual. | Optional: repeat the nontrivial object, disjoint domains, total substitution map, and quantifier over complementary pairs, referring only to the displayed representation equations. This is not a missing-hypothesis finding. |

The abstract, arity, notation, and consolidation edits are implemented in the final reviewed source. The optional expansion of the representation-theorem statement is not needed for the present local reading and remains an optional editorial preference, not a missing-hypothesis finding.

## Definition-order and notation audit

- The restriction and range axioms precede `D`, `D_!`, the local adjunction, and the Hoare constructions. The functors' source and target categories appear before their object and morphism actions. The coend convention includes the opposite arrow explicitly.
- Complementary pairs, separation, and inseparability precede the transfer theorem. Its witness projections, proof maps, range equalities, and commuting equations are typed. The Turing section separately supplies parameter universality and binary case distinction before proving their consequence.
- The numerical category on positive finite powers of the natural numbers is introduced before its split completion. The split category and its total arrows are defined before the slice category is used. The text explicitly locates restriction domains in the partial split category, rather than treating them as nonidentity restriction idempotents in the total category.
- In §9, the polynomial functor on families is typed before its formula and morphism action. The composition product, unit, and structural constraints are specified. The two coactions and their compatibility are stated. The backward premise map has the correct displayed type. The revised source now defines the notation `y^B` and `Sy` locally.
- In §10, the recursive rule presentation precedes `P_Σ`. The finite-proof theorem explains the carrier, structure map, and universal fold, including computability of the fold. The presentation category and its identity/composition laws precede `Proof_S`. The range functor and its natural monomorphism have explicit domains, codomains, and actions on commuting squares.
- In §11, `R_H` and `L_H` are typed between covariant functor categories. The opposite-arrow action is explicit. The right Kan extension is identified together with its type and adjunction. The comparison does not conflate a functor-category right adjoint with a computable weakest liberal precondition.
- In §12, the raw negation constructor is defined on formula codes. Refutations are constructed as a pullback, with their range identified by inverse image. The later negation functor on the deductive category is contravariant; double negation is an isomorphism there, and an involution only after the stated quotient. These distinctions should be retained.
- The statement and proof of essential incompleteness distinguish consistency of an extension from truth in the valuation used to establish base consistency. This qualification performs a mathematical function and should not be removed as a disclaimer.
- The arithmetic coding and free-variable substitution algorithm are defined before the representation corollary. Its numeralwise hypothesis is explicit. The interpretation proposition is conditional; it does not claim an already constructed interpretation in Robinson arithmetic.

The prose pass found no prompts, model instructions, chat references, revision narration, review outcomes, or compilation remarks in the mathematical text. The separate outline and review reports contain the editorial material, as required. LaTeX labels containing “certificate” are internal cross-reference identifiers, not claims of a complexity-theoretic certificate notion in the prose.

## Organization

No reordering is required. The redundant opening of §13 has been deleted and the cofree comparison is retained at the existing §10 discussion. The genuine open problem remains in §13. The semantic nonrepresentability theorem, the singleton-precondition counterexample, and the distinction between raw negation and complement each have a concrete mathematical function and should remain.

## Exact replacement wording and implementation

The integrated abstract states:

```latex
Typed inference rules determine
polynomial functors. For recursive presentations with at most two premises
per rule, finite proofs form their initial algebras in the total category
obtained by splitting numerical restriction idempotents.
```

The normalization sentence in §10 has been restricted as recommended:

```latex
A c.e. list of rules with at most two premises can be presented in this
form by including a finite enumeration witness in each rule instance,
provided the premise and conclusion maps are computable from that
witnessed instance.
```

The notation is now specified immediately after defining the composition unit:

```latex
Write $y^B(X)=X^B$ and $Sy=\coprod_{s\in S}y$.
```

The §13 monograph paragraph retains its source claim. Its final sentence is now:

```latex
For the existence problem above, the relevant universal property is
the initial-algebra property of Theorem~\ref{poly:initial}.
```

## Scope and final-snapshot status

The entire assembled source and outline were read. The governing writing source was consulted in the portions stated above. New monograph references were checked against the supplied July 2024 draft: the composition product on printed p. 180, cofree-tree example on p. 295, cofree-comonoid theorem on p. 315, bicomodule definition on p. 332, Garner correspondence on p. 336, and the coding question on p. 350. Older bibliography claims were not independently rechecked in this editorial pass.

This report does not certify all proofs or novelty. The separate hostile-referee audit addresses mathematical validity and scope. Compilation and rendered-page verification belong to the assembling author's checks; this report does not claim to have performed a full visual inspection.

Final-snapshot check: the abstract, arity qualification, local polynomial notation, consolidation of the cofree discussion, and removal of the §13 recap were verified in the assembled source. The added paragraph in §10 explicitly extends the numerical range, product, and stable-union constructions to the split category; it introduces a mathematical fact needed by the later application and contains no process commentary. The final checked compilation log has no warning or box-warning matches. Full rendered-page inspection remains the assembling author's separately reported check.

**Final reviewed source SHA-256:** `433f8a30df4f6d84e6055ac1d96ec58225e765e9f01354a8fd6794fd0ed226f0`.

A final local check also verified deletion of the unproved nonimplication about finite joins and initial algebras in §13. The paragraph now states the concrete ingredients used by the numerical construction and the corresponding abstract existence question. No required editorial repair remains in this snapshot.
