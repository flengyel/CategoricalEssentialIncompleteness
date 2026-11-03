# Continuation: review the introduction with multiple agents

These are retained instructions for the v12 introduction review.
The current target is v46; use [docs/CODEX_WSL2_V46.txt](docs/CODEX_WSL2_V46.txt)
for new implementation. The earlier task text is preserved below.

## Task and accepted baseline

Continue work on **Local connectedness in recursion categories and essential incompleteness** in [flengyel/CategoricalEssentialIncompleteness](https://github.com/flengyel/CategoricalEssentialIncompleteness).

The author has accepted the version 12 abstract. The next task is a coordinated review of the introduction, followed by one checked proposal for its revision. Read the paper and its proofs before deciding what the introduction should say. Do not resume the earlier cycle of replacing isolated phrases in the abstract.

The manuscript baseline is commit `cceacb7725c0dd057caeff0579e90afb3f7ae00c`, version 12, dated 31 October 2026. Fetch the current repository state and check for subsequent changes before working. Preserve existing uncommitted work. The source is modular:

- Assembly: `manuscript/latex/main.tex`.
- Introduction: `manuscript/latex/sections/01-introduction.tex`.
- Accepted abstract: `manuscript/latex/abstract.tex`.
- Preamble and version: `manuscript/latex/preamble.tex`.
- Sections, appendices, and bibliography: the corresponding files under `manuscript/latex/`.
- Version 12 PDF: `manuscript/archive/essential_incompleteness_via_local_connectedness_v12.pdf`.
- Existing outline and writing review: `Audit/2026-10-31-outline-v12/README.md`.
- Theorem and proof synopsis prepared for this continuation: `notes/manuscript_v12_theorems_and_proofs.md`.
- Local build and revision instructions: `manuscript/latex/README.md`.

The synopsis and earlier reviews are reading aids. Check assertions against the manuscript; earlier agent agreement is not evidence of correctness. The separate note `notes/deductively_closed_subobjects.md` is not part of the manuscript. Do not silently import its proposed general construction into the introduction.

## Required reading and writing sources

Use the **mathematical-writing:revise-mathematical-prose** plugin and read its current instructions and supporting references. Inform the author that it is being used. If a hostile-review plugin is used, identify its work as an author-side audit; do not manufacture defects or imitate a journal decision without evidence.

Before submitting an evaluation, **each reviewing agent must read the complete current manuscript**, including the accepted abstract, all sections, appendices, and bibliography, **and the complete Knuth–Larrabee–Roberts report**. The coordinator must also read both. Specialized assignments below determine the emphasis of each report, not permission to omit this common reading.

Use the official sources:

- [Knuth, Larrabee, and Roberts, *Mathematical Writing*: Stanford report](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf).
- [Bibliographic information and errata](https://www-cs-faculty.stanford.edu/~knuth/klr.html).

The report used for the version 12 review has 117 PDF pages; printed page 1 is PDF page 3. Check that a retrieved file is an actual readable PDF. An old locally cached file was invalid; possession of a filename is not evidence of source access. Record actual reading coverage. Do not claim memorization, complete reading, or verified compliance without performing the corresponding work. If access fails, seek another primary copy; record any remaining limitation and label the affected review provisional.

After the complete reading, return particularly to §1, pp. 2–5, on motivation, connected exposition, openings, and jargon; §§4–5, pp. 9–13, on definition timing; Wilf, §27, p. 59, on stating results promptly; Ullman, §30, p. 67, on types and antecedents; Lamport, §§31–32, pp. 69–71, on structure and unnecessary prose; and Halmos, §42, pp. 106 and 111–112, on organization. Attribute guest speakers accurately. Distinguish verified source advice, the plugin's supplementary conventions, and independent editorial judgment. The report does not supply a universal template for an introduction.

Read Heller's 1990 paper as an additional model of mathematical exposition. Use the actual text, not an imagined imitation of its style. Verify historical and mathematical literature claims from primary sources. For Lengyel 2004, consult the corrections in `flengyel/errata` at the version cited in the manuscript; distinguish any later corrections instead of silently changing the source of a claim.

## Independent review: five agents and one coordinator

Give the five reviewers the same source snapshot and the common reading instructions. Initially give them no coordinator-written replacement introduction. Each should derive the contribution and proposed organization independently from the results. Reviewers should not edit manuscript files. The coordinator is responsible for synthesis and any authorized implementation.

| Agent | Main responsibility | Required questions |
|---|---|---|
| 1. Contribution and organization | The central question, the contribution, and the introduction's paragraph order. | What does the paper prove? How do the categorical construction and the logical conclusions depend on one another? Which results deserve the opening paragraphs? Does the actual roadmap describe the paper? |
| 2. Categorical statements and proofs | Types, hypotheses, theorem scope, and dependencies. | Does each introductory claim accurately summarize Theorem 3.3 or Corollary 3.5? Where are the source, target, lifting assumption, and logical interpretation supplied? Is a claim about a category being substituted for a claim about an external theory? |
| 3. Examples and incompleteness | Miller, arithmetic, cosheaves, and their permitted extensions. | What precisely is incomplete, under which computability conditions, and why does the categorical result imply it? What does the Miller functor counterexample establish? What does Corollary 9.3 add to the presentation? |
| 4. Literature and attribution | Primary-source verification and mathematical positioning. | What did Di Paola–Heller propose? Which assertions are due to Heller, Montagna, Di Paola–Montagna, Miller, Bauer–Hanson, Cockett–Lack, and Lengyel? Is each citation an antecedent, a tool, or a comparison? Are priority or generalization claims actually supported? |
| 5. Prose, terminology, and reading order | A sentence-by-sentence introduction review using KLR. | Does every paragraph have a mathematical function? Are terms and antecedents intelligible in reading order? Are sentences compressed, repetitive, defensive, or empty? Does prose explain an implication rather than merely list named objects? |

Every report must contain:

1. A two- or three-sentence account of the contribution, written independently from the results.
2. The introduction's actual paragraph outline, assigning each paragraph a function: problem, construction, result, proof explanation, comparison, or roadmap.
3. An evidence table: exact introduction passage; theorem/proof/citation anchor; actual difficulty; necessary correction or optional improvement; proposed repair.
4. A terminology audit of every mathematical expression in the introduction: its referent and type where applicable; standard term or paper-specific convention; first explanation and formal definition; absent, late, inconsistent, or adequate. Search the full paper before claiming that a definition is missing.
5. A proposed paragraph outline, naming the results or sources that justify each paragraph.
6. A coverage and uncertainty record: what was read; which proofs and references were checked independently; unresolved questions.

Use section numbers, theorem labels, and PDF pages for findings about the manuscript. Use precise primary-source locations for literature claims, and section/printed page/speaker for KLR advice. A suspected mathematical gap must identify the exact inference; a poor sentence is not a theorem counterexample. Preserve passages that work.

## Mathematical structure that must survive the review

The synopsis gives full statement and proof outlines. Check these distinctions in the manuscript itself:

1. **Theorem 3.3 constructs an inseparable pair.** Its source already is a recursion category and has a Turing morphism. A range functor does not create that morphism. The target has the additional structure stated in the theorem; local connectedness alone is insufficient. The sections associated with complementary source domains must lift. Proposition 3.4 gives a sufficient condition, and Appendix C proves that the lifting condition cannot simply be omitted.
2. **Corollary 3.5 gives a conditional algebraic implication.** The concrete logical constructions separately supply syntax, derivations, deductively closed theorem sets, and the reduction inequalities. Completeness of a consistent extension in the specified class would produce the forbidden separation. Do not claim a general construction of theories in every restriction or recursion category.
3. **The Miller section is a principal contribution.** It constructs a recursion category of partial functions computed with the same values and domains from every binary representation of the sequence. The categorical diagonal pair reduces to the index sets below and above one half. These yield the real-closed-field theory. Preserve uniform semidecidability of the axiom set from **all** binary representations. A fixed representation can compute a separator, giving a faithful range functor preserving restriction products that does not preserve the specified inseparable pair or Turing morphism.
4. **The arithmetic proof uses the numerical recursion category.** Finite computation proofs connect the categorical pair to PA-provability and refutability. The conclusion concerns every consistent computably enumerable extension of PA.
5. **The syntactic-category results are a distinct branch.** Sections 5–7 construct model functors and prove inseparability in `S_T`, compatibly with theory extension. They do not by themselves prove incompleteness of the external theory `T`. Section 8 explicitly demonstrates the distinction with the complete theory of the standard natural numbers.
6. **The cosheaf construction produces specified theories.** Formula and derivation functors are constructed in the total category, and component evaluation gives sets of formulas and derivations. Theorem sets, after deductive closure and consistency have been established, determine partial identities. An arbitrary restriction idempotent is not a consistent theory or extension.
7. **Corollary 9.3 gives endpoint essential incompleteness.** For each endpoint 1 or 2, every consistent extension in the same propositional language with a c.e. axiom set is incomplete. The proof embeds that extension in a compatible family by retaining the other base components. Do not extend this conclusion to component 0 without a proof.
8. **The two completion constructions are distinct.** Restriction-idempotent splitting is defined following Cockett–Lack. The full Karoubi-envelope equivalence in this example additionally uses the splitting of arbitrary idempotents through their component images, proved in Corollary A.9. Explain the relevant construction without identifying a theory with an idempotent.

The introduction should make the categorical route to essential incompleteness intelligible, give the Miller result its appropriate prominence, state the arithmetic and cosheaf conclusions, and position the separate syntactic-category branch and prior work accurately. Decide the exact paragraph order from the independent reports. Do not reproduce the entire preliminaries section or turn the introduction into an inventory of technical objects.

## Author's terminology and prose requirements

- **Never move between levels without the defined map or construction.** Distinguish a theory from its theorem set, a set from its partial identity, a derivation from its conclusion, an index from its denoted function, and a category from a chosen presentation.
- Use **morphism** in prose. Preserve the LaTeX `\arrow` command in diagrams and the wording of bibliographic titles.
- Do not use **classical** or ornamental adjectives. State the mathematical property or identify the category explicitly.
- Use established mathematical terminology. Do not introduce “support” for a restriction domain, “binary names,” “rows” of a binary sequence, “formal numerical types,” or new informal labels for structures already named in the literature.
- Use **Turing morphism** for categorical universality. Numerical and oracle programs may be discussed where the relevant computation model and index types have been specified; do not import those instantiations into the abstract categorical argument.
- Do not use “proof object” or “sentence object” as an unexplained substitute for an actual construction. The paper supplies precise constructions in Appendix B and the logical sections. Introduce them only if their role belongs in the introduction, with their referents clear.
- Give every displayed morphism and functor its source and target. Check variables, quantifiers, composition, variance, and equality notions. Retain necessary hypotheses. Do not repeat elementary arguments already available from Montagna merely to make the prose appear self-contained.
- Avoid missing antecedents such as “the criterion,” “the proof,” “this,” or “its” where more than one referent is possible. Do not replace them with another undefined phrase.
- Remove empty transitions, repeated qualifications, defensive disclaimers, and overly compressed sentences. Retain substantive counterexamples and distinctions needed by an inference.
- Keep all prompts, review records, uncertainty logs, and editorial commentary outside the manuscript, including outside its source comments.

## Coordinator synthesis and final checks

First compare the independent contribution statements and outlines. Resolve disagreements against the paper and primary sources, not by majority vote. Produce a consolidated claim-to-result table and a paragraph outline before drafting prose. Explain the purpose of each proposed move or deletion. A term that is defined later is not automatically defective in an introduction; judge whether the intended mathematical reader can understand its role.

Then write **one complete proposed introduction**, preserving relevant attribution and theorem references. Do not supply a menu of competing openings. Have at least two reviewers check the exact proposed text: one for mathematical claims and levels, another for organization and prose. The literature reviewer should verify any new or changed historical claim. Correct their supported findings and reread the entire introduction continuously.

The review deliverables are:

- Five independent reports with reading-coverage records.
- A consolidated introduction outline and claim-to-result table.
- One checked replacement introduction and a concise explanation of substantive changes.
- A list of mathematical or bibliographic questions that remain unresolved, if any.

Save these outside the manuscript, for example under `Audit/<date>-introduction-review/`. If the current continuation request is review-only, deliver the checked proposal without altering the manuscript. If revision is authorized, the coordinator should implement the introduction changes, make only necessary consequential edits, and complete the build and publication workflow. Do not invent a new permission requirement for actions already authorized by the author.

For an implemented manuscript revision, increment the version from the current repository version, update the title date and current-version links, build `main.tex`, resolve reference/citation and layout warnings, inspect the rendered introduction and adjacent pages, and retain a PDF with the new version in its filename. Version 12 is the baseline; if no later revision intervenes, the next manuscript version is 13. A continuation prompt or review report alone does not require changing the manuscript version. The author's standing instruction to push completed authorized changes to `main` remains in force; verify the remote result and preserve intervening work. Do not claim a Lean check: the current manuscript has not been reconciled with the version 5 Lean development.

## Accepted version 12 abstract

This is a record of the author's accepted text, not a new revision target:

> We derive essential incompleteness from a categorical construction of inseparable pairs. The construction uses a lifting theorem for range functors into locally connected restriction categories. We recover recursive inseparability of the theorem and refutation sets of every consistent computably enumerable extension of Peano arithmetic. From Miller's sequence we construct a recursion category and a consistent theory of real closed fields. Every consistent extension of this theory whose axiom set is semidecidable uniformly from all binary representations of the sequence is incomplete. The Miller example also gives a faithful range functor preserving restriction products that sends an inseparable pair to a separable pair. The same categorical method, applied to a recursion category constructed from cosheaves on a three-point space, gives essentially incomplete propositional theories.
