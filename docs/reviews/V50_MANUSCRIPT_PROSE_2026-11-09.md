# Manuscript prose review: version 50

Version 49 already contains no instances of the empty modifiers “actual,”
“genuine,” “historical,” or “legacy.” This pass removes one redundant sentence,
expands compressed noun phrases, and clarifies references to mathematical
objects. The approved abstract and the mathematical content are preserved.

The source reviewed is *Logical consequence and essential incompleteness in
recursion categories*, v49 at
`c5d7d0e3a6b64d7546002a908d79c2a11db2a9dc`. All 22 TeX files were read,
including the four appendices, headings, comments, diagrams, and bibliography.
The v49 changes were compared with the preceding v48 source and preserved.
The revised version is v50, dated 9 November 2026.

## Existing outline and dependencies

The paper constructs internal deduction in completions of recursion categories
and applies categorical inseparability to consistent extensions. The order
supports those dependencies and is retained.

| Part, with subsections in reading order | Mathematical function |
| --- | --- |
| Abstract | States the internal construction and the arithmetic, Miller, and propositional incompleteness results. |
| 1. Introduction; related work | States the problem, distinguishes the two comparison criteria, identifies the three applications, and relates them to the cited constructions. |
| 2. Partial maps and restriction idempotents; products, coproducts, and local connectedness; recursion categories | Fixes composition, restrictions, ranges, splitting, functor preservation, and the Turing property. |
| 3. The comparison theorem; complementary conditionals | Proves the diagonal comparison and source inseparability criteria. |
| 4. Theories and their interpretation; incompleteness from semantic consistency; inseparability in the source | Represents sentence theories by ranges, extends interpretation through splitting, and applies the two criteria. |
| 5. The syntactic recursion category; total restriction splitting; syntax and lists; free variables and substitution; derivations and theories | Constructs the arithmetic presentation, proves regularity and extensivity, and realizes syntax and derivation initiality with parameters. |
| 6. Interpretation and soundness; lifting complementary conditionals; total interpretation; standard codes; ultrapowers | Establishes the preservation and soundness results used by the arithmetic comparison. |
| 7. Comparison in the fixed syntactic category; indexed theories; uniform independent sentences; numerical realization; numerical incompleteness; numeral instances and theory extension | Applies the comparison to arithmetic, constructs a uniform sentence morphism, and compares numerical and syntactic realizations. |
| 8. Computation independent of binary representation; index sets below and above one half; a theory of real closed fields | Constructs the Miller recursion category, reduces its diagonal pair to the cut sets, and proves essential incompleteness for represented extensions. |
| 9. Three-point space; complementary restriction idempotents; evaluation functors; propositional theories and component theorem sets | Constructs the cosheaf example and obtains the two essentially incomplete propositional theories. |
| A. Categorical hypotheses; terms, formulas, and free variables; admissible substitution; inference rules; first-order theories; propositional theories | Supplies the general syntax, substitution, and least-image constructions used in the applications. |
| B. Cosheaves and functor categories; partial maps and ranges; universal object and frame; Turing morphism; recursion category and splitting | Proves the category and universal-property assertions used in Section 9. |
| C. Necessity of section lifting | Gives a counterexample to omitting the lifting hypothesis. |
| D. Faithful families and theory extension; inseparable pairs; numeral observations; complete ambient theory | Constructs the family interpretation and distinguishes source inseparability from incompleteness of the ambient theory. |
| Bibliography | Records the sources cited in the constructions and comparisons. |

## Editorial source and repairs

Consulted Knuth, Larrabee, and Roberts,
[*Mathematical Writing*](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf),
§1, §§4–5, and the Lamport discussion in §§31–32. Relevant advice concerns
self-contained statements, consistent notation, readable sentences, and
unnecessary jargon and strings of nouns. The preference for Došen–Petrić
economy and “morphism” is the author's convention. These local repairs apply
that guidance; they are not quotations from it.

| Location | Before | Implemented repair |
| --- | --- | --- |
| Introduction, paragraph on generated theories | “The computational criteria apply to these theorem and refutation restriction idempotents.” | Deleted: the next paragraph states the criteria and their application. |
| Section 5, computation coding | “output-extraction function” | “function that extracts the output.” |
| Lemma 5.2 proof | “the first successful test's first component” | “the first component of the least successful code,” matching the increasing numerical search. |
| Lemma 5.3 proof | “The search correctness statement” | “The correctness of the search.” |
| Section 5.2, constructor predicates | “constructor decomposition equivalences”; “coefficient-carrier predicate” | “equivalences describing constructor decomposition”; “predicate for its coefficient object.” |
| Proposition 5.5 proof | “syntax-carrier predicate”; “operation-trace requirements” | “term or formula predicate”; “requirements on operation traces.” |
| Proposition 5.7 proof | “source-restricted graph equations” | “graph equations restricted to their sources.” |
| Lemma 5.8 proof | “node-membership and computation witnesses”; “finite-sequence argument” | “witnesses for node membership and computations”; “argument for finite sequences.” |
| Section 6.3 | “full conclusion morphism”; “constructor realization” | “conclusion morphism”; “interpretation of the constructors.” |
| Sections 7.1 and 7.4 | “full conclusion morphism”; “full derivation conclusion” | “conclusion morphism for all formulas,” explicitly distinguishing it from the pullback to sentences. |
| Section 7.2 | “family axiom subobject”; “two slice-morphism components” | “axiom subobject for the family”; “two slice morphisms.” |
| Section 7.4, derivation validity | “each stored label has this membership” | “each stored label belongs to $\widehat{R_n}$ for its node's arity $n$.” |
| Lemma 8.1 proof | “the asserted output and definedness” | “computes $\tau_z$ from every binary representation of $z$.” |
| Section 9.3, atomic axioms | “positive and negative atomic axiom morphism” | “morphism … inserting the positive and negative atomic axioms.” |
| Theorem 9.5 proof | “atom map” | “atom morphism.” |
| Proposition B.1 proof | “morphism of pushouts” | “morphism between the pushouts.” |
| Proposition B.2 proof | “These morphisms are recursive” | “Their components are recursive,” distinguishing the natural transformation from its numerical functions. |
| Corollary D.2 | “identically defined inseparable pair” | “inseparable pair defined by the same formulas.” |
| Appendix D, after equation (37) | `T-provably` | `$T$-provably`, typesetting the theory symbol. |

## Definitions, notation, and retained distinctions

Restriction, range, splitting, and the Turing property are defined in Section 2
before the comparison criteria. The interpretation functors are introduced
with source and target categories. The syntax constructors, coefficient
objects, rule objects, and parameter slices precede their applications.
The changed references to $\widehat{R_n}$ and $\tau_z$ name objects already
defined in their respective constructions. No new terminology is introduced.

“Canonical” is retained for comparisons determined by universal properties;
“full” remains for full subcategories and functors. “Standard” distinguishes
standard arithmetic codes from nonstandard ones. “Exactly” and “precisely”
remain where they express domain equality or a biconditional. The differences
between uniform and pointwise provability, representation-independent and
fixed-oracle computation, and partial substitution and its admissibility
condition are retained. The counterexamples in the appendices are substantive
mathematics and remain in place.

## Checks and relation to Lean

- The approved abstract and bibliography are byte-identical to v49.
- All displayed mathematics, diagrams, labels, references, and citation commands
  are unchanged. The 62 numbered results and three definitions are retained.
  Corollary D.2 has the prose-only replacement listed above; the other 64
  statement and definition environments are byte-identical.
- The inserted inline mathematics consists only of references to
  $\widehat{R_n}$, $n$, and $\tau_z$, and mathematical typesetting of the existing
  symbol $T$. Hypotheses, conclusions, definitions, and proof arguments are
  unchanged.
- The PDF builds to 73 pages without LaTeX warnings, undefined references,
  missing-character warnings, or overfull boxes. Rendered pages 1, 12, 16, 27,
  31, 38, 42, 50, 61, 62, 70, and 71 were inspected.
- `python3 scripts/verify.py --manuscript-only` passes for v50, including the
  manifest, source archive, PDF copies, correspondence version, and audit entry
  paths. The source archive contains the 22 TeX files and their README.
- No Lean file or pinned dependency changes. The next integrated verification
  of the Palomar port must use v50. This pass did not rerun Lean or re-audit the
  external mathematical references.

Machine-readable checks are in
[V50_MANUSCRIPT_VERIFICATION_2026-11-09.json](../V50_MANUSCRIPT_VERIFICATION_2026-11-09.json).
