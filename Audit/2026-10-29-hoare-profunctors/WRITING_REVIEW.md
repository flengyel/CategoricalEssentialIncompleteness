# Mathematical-writing review

The account has a coherent mathematical progression: computational domains lead to Hoare profunctors, the separation theorems specify the deductive data required for incompleteness, and the numerical construction realizes the proof-code hypotheses. Closure operators and the category of deductive presentations now appear in Appendix A, where their precise role is clear. The principal repairs to variance, statement scope, notation, and duplication have been implemented. The explicit intrinsic construction problem is mathematically substantive and remains part of the account.

**Manuscript:** Florian Lengyel, *Domains, Hoare profunctors, and essential incompleteness*, 29 October 2026. Reviewed the complete assembled LaTeX account, including all nine main sections, four appendices, bibliography, revised trace-formula paragraph, and final short additions defining the computability terminology and identifying predicate-transformer semantics. This report supersedes the review of the earlier arrangement. The final reviewed source fingerprint is recorded below.

**Final source SHA-256:** `54860cdd4e7a93c3e2de4abc5c8e39d2332384fde14706e143536a486dd26a83`.

**Governing source:** Donald E. Knuth, Tracy Larrabee, and Paul M. Roberts, *Mathematical Writing*, supplied PDF `knuth_mathematical_writing.pdf`. Directly read §1, printed pp. 1–5 (PDF pp. 3–7), and §§4–5, printed pp. 9–13 (PDF pp. 11–15). The recommendations below distinguish that source from the mathematical-writing skill's independent conventions.

## Actual outline and dependencies

1. **Computation, assertions, and deduction.** States the problem and distinguishes computational domains, Hoare relations, and deductive presentations; identifies the relevant literature.
2. **Restriction domains and direct images.** Defines restriction and range structure, the contravariant domain functor, direct images, and the local adjunction. These definitions support all subsequent Hoare constructions.
3. **Hoare assertions as profunctors.** Defines profunctors and their composition, then proves the total- and partial-correctness pseudofunctor laws, comparison, program-order variance, and detection of domains.
4. **Weakest liberal preconditions and representability.** Defines representing domains and the associated right adjoint. **§4.1** proves the exact numerical characterization and distinguishes existence, uniform synthesis, formula construction, and membership decisions.
5. **Stable unions of domains.** States the additional universal range property, defines Heller unions, proves their preservation laws, and types the bounded-distributive-lattice-valued domain functor. These laws are used by the separation arguments.
6. **Categorical separation and proof codes.** Proves the transfer theorem from an inseparable pair and positive/negative proof maps. **§6.1** proves the distinct representation-based inseparability theorem.
7. **The numerical category and effective unions.** Defines the partial-recursive category and verifies its range and uniform-union properties. The example at the end distinguishes uniform effective unions from arbitrary increasing unions.
8. **A numerical deductive construction.** **§8.1** constructs an inseparable pair, computation evidence, syntax, axioms, and decidable annotated proof checking. **§8.2** constructs the Boolean deductive category and proves essential incompleteness. **§8.3** connects the assertions to the Hoare relations and constructs the proof-conclusion maps. **§8.4** proves the conditional arithmetic representation corollary, including jointly recursive numeral substitution. **§8.5** gives an interpretation criterion and the comparison with effective verification.
9. **The intrinsic construction problem.** Identifies the additional categorical construction and arithmetic comparison questions; explains why unrestricted complementation would remove the computational separation condition.
A. **Closure operators associated with deductive presentations.** Constructs least closure for specified rules and axioms when the deduction stages admit stable unions. **§A.1** defines `Cons`, the contravariant theory and domain functors, and their natural inclusion. **§A.2** verifies the effective numerical deduction stages and compares their closure with the already defined propositional calculus.
B. **Ordinary interpretations and finite hom-sets.** Proves the collapse obstruction for locally finite targets.
C. **Adjoining partial witnesses to a profunctor.** Defines the coend extension, proves its support law, and recovers the total-support fibre.
D. **Indexed predicates and enrichment.** States Kelly's required monoidal and hom-object data, distinguishes indexed predicates, and separates logical negation from inverse image along a negation-code map.

The implemented reorganization is appropriate: the main argument first defines the numerical calculus directly, and Appendix A then identifies its closure operator. Thus the closure construction does not appear to supply the missing intrinsic deductive data. No further reorganization is needed.

## Findings and repairs

| Anchor | Original difficulty | Source principle or independent rationale | Repair and status in the reordered snapshot |
|---|---|---|---|
| Abstract, original phrase “all such preconditions are computably enumerable” | The range of postconditions was not explicit. On the full powerset the assertion is false even for the identity. | Knuth et al., §1 point 17: readable, unambiguous statements; mathematical quantifier precision. | Implemented: the abstract gives the exact right-adjoint characterization on computably enumerable domains, with the term spelled out. |
| §3, coend relation before `hp:hoare-types` | The displayed `Q(u,1)` suppressed the opposite arrow although `Q` has source `B^{op} × C`. | Explicit typing convention requested for this manuscript; §1 point 14 on consistent notation. | Implemented as `Q(u^{\op},1)`; the fixed target identity is determined by the displayed types. |
| §A.1, closure example after the naturality square | The same letter `c` denoted a closure operator and an element of its underlying three-element set. | §1 point 14: distinct notation for distinct objects. | Implemented: the third element is `z`; the operator is described in words. The counterexample to join preservation remains. |
| §8.2, negation functor | “The double application of `N_T`” left mixed variance implicit. | Manuscript typing convention; §1 points 11 and 14. | Implemented: opposite-arrow action and `1_{\mathcal B_T}\cong N_T\circ N_T^{\op}` are explicit. |
| §8.5, former repeated wp/wlp definitions and extreme identities | These duplicated §4.1 without adding a new explanation. | Skill economy requirement; Knuth et al., §1 points 10–13 require explanatory, connected prose rather than repeated formulas. | Implemented: finite-trace formulas supply the new information and refer back to `hp:halting-predicates`. |
| §9, former “conditional arithmetic theorem below” | The theorem precedes the discussion. | §1 point 17; accurate cross-reference. | Implemented: the exact reference is `Corollary~\ref{num:recursive-representation}`. |
| Proposition `num:interpretation` | Its statement used `A,B` from §8.1 without recalling their inseparability. | §1 point 5: theorem statements should usually be self-contained. | Implemented: the statement begins by fixing a disjoint recursively inseparable c.e. pair. |
| First sentence of §2 and end of the syntax paragraph in §8.1 | The composition convention was repeated immediately after §1; the complete grammar already determined that it is propositional. | Independent economy requirement. | Implemented: both redundant sentences are removed. |
| Throughout, “computation certificate” and “proof certificate” | No polynomial-time certificate convention is needed or established. This is a terminology issue, not a flaw in decidable finite checking. | Supplementary `terminology.md`, not a rule attributed to Knuth et al. | Implemented throughout the body using “computation code”, “annotated proof”, and “proof code”; the abstract uses “finite proofs”. Internal LaTeX label names need not change. |

## Definition-order and notation audit

The domain functor `D:R^{op}→Pos`, direct-image functor, and the two Hoare profunctors are typed before their actions are given. Both object and morphism actions are supplied. The category `Cons` has explicitly specified objects, morphisms, identity, and composition; its identities are the selected restriction domains, as required by the stated splitting convention. The naturality square of the inclusion of theories is written and justified. The fixed-point inclusion is correctly treated in a `Pos`-valued functor category.

The definitions of complement, separation, inseparability, consistency, and completeness precede their use in the separator theorem. The numerical grammar, proof relation, theories, consistency, and completeness precede the numerical theorem. A numerical theory is now defined directly as a set containing the tautologies and closed under modus ponens; its fixed-point characterization is proved later in Appendix A. The coend extension and its support map are typed before their laws. Kelly's monoidal category and hom-object types precede the enrichment comparison.

The same letters are reused in separate sections for local objects; those uses are declared and do not create a dependency ambiguity. The simultaneous overload in the closure example is removed. “Turing morphism” is cited as standard recursion-category terminology in §7 and explained informally in §9; its full axioms are not used in any proof of this note. This is acceptable for the stated mathematical audience, but the citation cannot substitute for such axioms if a later theorem begins to use them.

The nonrepresentability theorem, failure of uniform synthesis, singleton-precondition counterexample, distinction between logical and computational negation, and separation of consistency from soundness each perform a mathematical function. They should not be deleted as purported defensive remarks. The open problem in §9 identifies a construction not supplied by the conditional theorems and is also substantive.

## Replacement wording and implementation

The final abstract wording is:

```latex
incompleteness under explicit hypotheses on representation or finite proofs.
```

The following earlier suggested replacements have been implemented verbatim or by mathematically equivalent wording. All editorial findings in the table are resolved.

For the negation functor paragraph:

```latex
It sends $\alpha$ to $\neg\alpha$ and sends
$a^{\op}:\beta\to\alpha$, where
$a:\alpha\to\beta$ is an arrow of $\mathcal B_T$, to the arrow
$\neg\beta\to\neg\alpha$ supplied by contraposition.
Double negation gives a natural isomorphism
$1_{\mathcal B_T}\cong N_T\circ N_T^{\op}$.
```

For the closure example:

```latex
For example, on $\mathcal P(\{a,b,z\})$, let $\mathrm{cl}$ add $z$
exactly when both $a$ and $b$ are present. The closed sets $\{a\}$ and
$\{b\}$ have closed join $\{a,b,z\}$, whereas their ambient join is
$\{a,b\}$.
```

For the abstract characterization:

```latex
For a partial recursive map, direct image on computably enumerable
domains has a right adjoint exactly when its domain is recursive.
```

## Scope

This is a complete-source editorial review of the identified reordered snapshot, including paragraph functions and definition order. Every manuscript paragraph introduces or defines a mathematical object, states or proves a result, explains a construction, distinguishes hypotheses, provides a counterexample, relates a source, or formulates a problem. The identified redundant sentences have been removed. No LLM-facing remarks, instructions, or editorial-process narration were found in the mathematical document.

The source and the generated table of contents were inspected. The compilation log at review time contained no undefined-reference or box-warning matches. Rendered-page visual inspection and final compilation are the assembling author's checks, not claimed by this report. This review does not certify all proofs, novelty, or the historical equivalence of the arithmetic representation convention with every usage in Di Paola--Heller. The substantive mathematical audit is separate.
