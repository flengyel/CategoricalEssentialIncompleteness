# Outline before revision

Baseline: 3f87a703c635c6c029f9c2bcb42aed5430ff8590.
Existing filenames: manuscript/syntactic_model_range_functors.tex and .pdf.
Requested new filenames:
manuscript/local_connectedness_and_essential_incompleteness.tex and .pdf.

## Existing outline

1. Introduction: a six-paragraph account of the program, lifting,
   syntactic models, effective observations, cosheaves, and roadmap.
2. The syntactic recursion category: restriction/domain notation and
   uniform provable program equality, with its computational structure.
3. Interpretation in models: the partial-graph functor for each model.
4. A faithful family and theory extension: the product target,
   faithfulness, target hypotheses, and the commuting extension square.
5. Switching and the local-connectedness theorem:
   connected-domain alternative, sections of partial injections,
   range-functor lifting, and its syntactic application.
6. Effective observations and essential incompleteness: the classical
   inseparable pair and its inclusion in proof/refutation sets.
7. Computational cosheaves and effective observation:
   computational fork diagrams, local connectedness, endpoint functors,
   categorical probes, and the theorem for computational extensions.

The committed twelve-page PDF contains the Introduction on pages 1–2.
The root checked its Git blob against the committed tree. This does not
identify the copy displayed to the user. The new basename will distinguish
the revision from earlier downloads with the same name.

## Confirmed structural issues

The opening does not develop the literature path supplied by LOCOct10f:
Rosolini's P-categories, Heller's existence theorem, and Lengyel's 2004
work are absent from both the introduction and bibliography. Bernardi is
mentioned only after the arithmetic proof. Technical abstract terminology
precedes its explanation in the body.

## Revised abstract outline

1. State essential incompleteness for consistent c.e. extensions of PA.
2. Explain the proof obstruction in ordinary recursion-theoretic language:
   disjoint c.e. sets with no recursive separator.
3. State the categorical contribution without undefined local notation:
   interpret programs in countable models, preserve domains and images,
   and lift the maps selecting between complementary domains.
4. State the nonnumerical application with its actual scope: the
   explicitly constructed computable propositional theories on the
   three-point space and their consistent computational extensions.

Exclude S_T, split restriction category, endpoint evaluation, atom map,
and unexplained lifting jargon from the abstract. Introduce those terms
in the body before they carry an argument.

## Revised introduction outline

### 1.1 Recursion categories and the incompleteness program

Adapt the opening of LOCOct10f directly: Di Paola–Heller's algebraic
motivation; partial computations and their domains; Rosolini's broader
setting. Explain recursive inseparability and its implication for
essential incompleteness, so that the problem precedes the machinery.
Place Bernardi's established precomplete-equivalence approach in this
context, stating its relevant conclusion rather than listing a citation.

### 1.2 Local connectedness and range functors

Define the connected-domain criterion and the range-functor action
before describing their roles. Explain Heller's local-connectedness
existence framework and the separate roles of range representation and
iteration in Lengyel 2004, using the corrected hypotheses.
Explain the precise lifting condition in LOC and why target structure
alone does not suffice.

### 1.3 Syntactic categories and the present applications

Define S_T informally by one uniform provable graph-equality sentence,
cite Montagna and Di Paola–Montagna, and explain their failure of local
connectedness. Present the model-family construction and its lift.
Distinguish internal inseparability from the effective argument that
uses numeral instances and c.e. proof search. State the three-point
application with its selected-domain scope, then give the roadmap.

## Body revision

Keep the proved construction and theorem hypotheses. Relocate definitions
currently delayed until use in later sections into the first technical
section: restriction structure, splitting, connected domains, weak choice,
range functors, and the recursion-category conventions needed by the
main theorem. Introduce formal numerical types, word frames, probes,
negation inverse images, and the computational-extension convention
where each first becomes necessary.

The mathematical-writing audit must record first occurrence, first
explanation, and formal definition for important terms. After the revised
source and PDF are checked, apply the hostile-referee plugin to the actual
revision, including its claims about earlier literature.

## Final implemented outline

The preceding sections preserve the plan prepared before editing. The
renamed source now implements the following layout, reviewed at SHA-256
`1078044059fe239c27fdc82a9b69e7995e3b28c03d7310ff1ffb4164948d439f`.

1. **Introduction**
   - **Recursion categories and incompleteness:** the Di Paola–Heller
     problem, Rosolini's framework, the separation obstruction, and
     Bernardi's alternative approach.
   - **Local connectedness and comparison functors:** connected domains,
     Heller's existence argument, corrected faithful iteration functors,
     the distinct range-functor theorem, and its lifting requirement.
   - **Syntactic categories and the present applications:** uniform
     provability in `S_T`; the failure of composition in the primed systems
     despite the qualified local-connectedness claim; faithful model
     interpretation; the separate effective arithmetic step; the
     three-point application; roadmap.
2. **Categorical preliminaries**
   - **Partial maps and domains:** restriction axioms, total arrows,
     domain and arrow orders, zeros, complements, inseparability, inverse
     images, ranges, and splitting.
   - **Products, coproducts, and local connectedness:** the typed
     structures, range functors, connected domains, sections, and weak
     choice.
   - **Recursion categories:** prodominical and isotypical conventions,
     the Turing-morphism property, and the adopted category definition.
3. **The syntactic recursion category:** numerical types, uniformly
   provable graph equality, well-defined composition, and the categorical
   computational structure.
4. **Interpretation in models:** typed object and arrow actions and their
   preservation laws.
5. **A faithful family and theory extension:** the product target,
   faithfulness and local connectedness, and the commuting extension
   square.
6. **Switching and the local-connectedness theorem**
   - **The local-connectedness construction:** the connected-domain
     alternative, the section proposition, and the full range-functor
     lifting theorem.
   - **Lifting in the syntactic category:** the single provably total
     selecting program and inseparability in every consistent `S_T`.
7. **Effective observations and essential incompleteness:** the actual
   numerical application of the local-connectedness theorem, the fixed
   pair's inclusion in proof/refutation sets, and the PA conclusion.
8. **Computational cosheaves and effective observation:** topology,
   cosheaves, computational fork diagrams, and the universal object.
   - **Local connectedness and lifting:** finite connected domains, full
     inclusion, and the nonnumericality invariant.
   - **Endpoint functors:** actions on spans, preservation, endpoint
     universality, probes, and observed carriers.
   - **Proof observations and extensions:** the chosen pair, syntax and
     logical rules, computational extensions, the functor to numerical
     pairs, and incompleteness.

The final abstract explains recursive inseparability directly and
describes the selection condition as two cases that the theory proves
disjoint and exhaustive. It does not require the reader to know `S_T`,
splitting, range-functor terminology, endpoint evaluation, or atom maps.
The first-use inventory and the disposition of all identified writing
issues are recorded in `WRITING_REVIEW.md`. The hostile mathematical
review follows this completed writing review.
