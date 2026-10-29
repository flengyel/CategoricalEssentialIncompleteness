# Terminology and prose review

This review covers version 16 of *Definability and incompleteness in recursion
categories*, the prose and declaration names in the 35 project Lean files,
and the current repository documentation. The complete manuscript source was
read. Imported Lean files were searched for the identified language patterns;
thirteen received comment-only revisions. Historical verification evidence was
retained as recorded.

The main defects were unnecessary specialist terminology, repeated assurances,
vague descriptions of maps and proofs, stale documentation, and redundant
recaps. This is a provisional editorial review: the official Stanford copy of
Knuth, Larrabee, and Roberts's *Mathematical Writing* could not be retrieved.
The repairs below follow the author's terminology instructions and explicit
editorial reasons; they are not presented as verified applications of passages
from that book. This review does not establish the origin of the wording or
certify every mathematical claim in the manuscript.

## Existing organization and mathematical functions

| Part | Subsections and function |
| --- | --- |
| 1. Introduction | States the incompleteness problem; compares the cited approaches; gives the organization. |
| 2. Definability algebras and categorical incompleteness | Defines enriched restriction and predicate data, the representation section, and morphisms; proves internal and external inseparability; defines Boolean presentations and proves the quotient theorem and decision equivalence. |
| 3. The numerical interpretation | Constructs the numerical and PER presentations and their exact-completion comparison; relates representation to strong numeralwise definability; constructs Lindenbaum quotients and interprets theory extensions; applies this to arithmetic. |
| 4. An equivariant recursion category | Gives the finite-group example and its Boolean presentation. |
| 5. Completions and introspective structures | Constructs restriction-terminal and exact completions, free introspective extensions, change of base, and the relative adjunction; compares definability with nonconstant introspection; derives numerical representation from arithmetic introspection. |
| Appendix A. Definability and introspection on a fixed base | Defines the enriched PA program category and proves the obstructions to internal representation and indexing, followed by the incomparability result. |

The central dependency remains representation section → inseparability →
Boolean-quotient incompleteness → numerical and arithmetic interpretation.
The organization supports that dependency; no replacement outline is proposed.

## Findings and implemented repairs

Page references below refer to the rebuilt PDF dated 28 October 2026. Source
labels and declaration names provide stable anchors.

| Location | Wording or issue | Editorial reason and repair |
| --- | --- | --- |
| §3, pp. 10–12; §3.2, pp. 14–15; numerical Lean modules | “tracker,” “tracked by,” `Tracker` | A representing partial recursive function can be described directly. Use “representing function” after stating partial recursiveness; rename the Lean type to `Representative` and its dependent API consistently. The distinction between a function and its morphism class remains explicit. |
| §4.1, p. 18, preceding `prop:equivariant-logical-model` | “an equivariant recursive witness for the union” | The phrase did not name the arrow. Display `D_(G × (D ∪ E)) → D_(G × D) + D_(G × E)`, state how it chooses a summand, and identify its composite with the copairing of inclusions. |
| §5.6, p. 28, proof of `thm:introspection-numerical-definability` | “The coverage used here” | Replace the vague noun with the equality of subobjects actually used: the two inverse images have join `1_ℕ`. |
| §1.1, p. 2; §5.6, p. 28 | “actual totality,” “actual total Boolean function” | State “totality on ℕ.” Retain the substantive distinction from totality provable in the theory. |
| End of §2; proofs of `prop:numerical-boolean-extensions` and `lem:pa-nonhalting-undecidable` | A repeated no-Boolean-map consequence; “This proves both implications”; “These are the two possible outputs” | Remove recaps that add no conclusion or justification. The theorem, corollary, and case analysis remain. |
| Project Lean docstrings, README, and formalization status | “genuine subobjects,” “actual equalizers,” “genuine regular epimorphisms” | These adjectives are not extra mathematical properties. State the constructions and universal properties directly. |
| `ParameterizedEqualizer.lean`, formerly `InternalBridge.lean` | “finite-limit bridge” | Name the construction: parameterized equalizer factorization. The module name and imports now use `ParameterizedEqualizer`; theorem names are unchanged. |
| `PCats/PCat.lean`, comment on restriction of pairing | “This is the crux; everything below is bookkeeping” | Replace the assessment with the equation and its meaning: restriction of a pairing is the product of the two restrictions. |
| `Metamath/Feferman/MPSequence.lean` | “proof bookkeeping”; a hard-coded old Mathlib revision; an unidentified “Appendix B of the manuscript” | Describe finite sequences of candidate formulas, remove the stale revision, and retain the concrete list of mathematical constructions the module does and does not provide. |
| `Metamath/Feferman/ProofCode.lean`; `PCats/OptionKleisli.lean`; `FailureOfComposition/Verification/CheckAxioms.lean` | “Numerical Gödel-style coding now exists”; “This is the model … lacked”; “axiom envelopes” | State the coding definitions, coproduct instances, and axiom dependencies directly. Remove repeated disclaimers and stale toolchain references; retain arithmetic representation limitations. |
| Project docstrings describing representation data | “remains a separate construction” | Replace the development-history wording with a reference to `GlobalRepresentation`, which supplies the data from the internal section. |
| `manuscript/README.md`, `NOTICE.md`, root README | Source described as an unchanged copy | Record the editorial revision and rebuilt PDF. Preserve the original provenance and record the revised hashes. |

“Tracker” was not an invented term. For example, Uemura explicitly uses it in
§5 of [*Cubical Assemblies, a Univalent and Impredicative Universe and a Failure
of Propositional Resizing*](https://drops.dagstuhl.de/opus/volltexte/2019/11411/pdf/LIPIcs-TYPES-2018-7.pdf).
Its replacement here follows the author's preference for direct terminology.

## Definitions, notation, and qualifications retained

- A PER and its support are defined before the numerical category's morphisms.
  A `Representative R S` is a partial recursive function, defined on the source
  support, respecting the two relations. A morphism is its equivalence class.
- Restriction idempotents, general predicates, and the maps `j_X` remain
  distinct. No arbitrary complement or c.e. hypothesis on a distinguished
  predicate was introduced.
- The objects `U` and `S`, the enriched base, and the numerical PER target
  remain distinct where the arguments require them.
- Program indices, partial functions, and morphism classes remain distinct.
  Numeralwise provability is still distinguished from a single universally
  quantified theorem, explicitly on p. 14.
- “Prodominical,” “isotype,” “near product,” “restriction idempotent,” and
  “introspective theory” were retained with their definitions or cited context.
  Unfamiliar terminology alone was not treated as an editorial defect.
- “Token,” “tag,” and “payload” in syntax-encoding implementations describe
  encoded data. This review found no reason to treat those programming terms
  as invented mathematical concepts.

## Scope and checks

All 64 LaTeX labels and all 19 bibliography keys are unchanged. The manuscript
contains no source comments or embedded editorial instructions. LaTeX builds
the 33-page PDF without warnings; rendered pages 1, 2, 10, 11, 14, 15, 18, and
28 were inspected. The mathematical statements and hypotheses are retained;
the union paragraph now supplies the type and defining composite of its map.

The thirteen imported-file revisions were checked by removing comments from
their before/after versions and comparing the remaining text exactly. Their
declarations and proofs are unchanged. Original hashes remain in
`SOURCE_PINS.json`; revised hashes and reasons are in `LOCAL_PATCHES.json`.
The original manuscript hashes remain in `MANUSCRIPT_SOURCE.json`.

The current Lean API no longer contains `Tracker`. Old verification logs retain
the declaration names that were audited at those commits. No compatibility
aliases with the old names were added. The audit lists use the new names.

The imported-source search was not a complete literary or mathematical review
of every dependency. The review also does not verify all bibliography claims,
the full mathematical program of the imported Rice–Shapiro development, or
any independent-kernel certification. Compilation and axiom-check results are
reported separately in this directory.
