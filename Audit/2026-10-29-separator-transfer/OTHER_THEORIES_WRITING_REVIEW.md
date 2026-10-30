# Writing review: other theories and precomplete equivalence relations

Date: 29 October 2026 (America/New_York). Reviewed file:
`OTHER_THEORIES.md`, read in full. This is an author-side editorial review
of a research audit record, not a journal referee report or a certification
of mathematical correctness or novelty. The source-access account belongs
in this separate report.

The exposition has a useful order: the relative theorem precedes its
translation construction, concrete applications precede the more general
precompleteness condition, and the lambda-theory example is separated from
the construction of syntactic recursion categories. The conditional scope
of the categorical assertions is visible. The initial local definition and
wording repairs have been applied. A final check also confirmed the explicit
equivalence-preservation requirement for general sentence translations.
No unresolved editorial issue remains in the reviewed note; no
reorganization was needed.

**Provisional source status.** The mathematical-writing plugin requires
Knuth, Larrabee, and Roberts, *Mathematical Writing*, as its governing
source. Requests for both the official Stanford report and its
bibliographic page timed out in this review session. No supplied copy was
available to this reviewer. The review is therefore provisional. Its
recommendations are supported by the explicit typing and editorial reasons
below, not by unverified quotations, numbered rules, or page references.

## Actual outline and dependencies

| Location | Function and prerequisites |
| --- | --- |
| Opening | States that a theorem about compatible presentations can have applications without a construction from every recursion category. |
| §1 | Recalls the extension argument for disjoint enlargements of a fixed inseparable pair; identifies the relative scope. |
| §2 | Defines the inverse-image theory `T^theta`, proves its consistency, effectivity, classical deductive closure, and completeness implication; then applies the existing `S_T` construction and gives extension and interpretation maps. |
| §3 | Checks the translation construction against `ACA_0`, finite set theory, and the negative translation into intuitionistic arithmetic; identifies the unverified weak-base cases. |
| §4 | Defines precompleteness numerically and in restriction notation, proves upward closure and numerical inseparability, and reconstructs the program-equivalence application. |
| §5 | Uses precompleteness of closed lambda-term conversion to obtain disjoint inseparable classes and rule out a maximal consistent c.e. lambda theory. |
| Sources and limits | Identifies the source locations, source-access limitations, and remaining nonnumerical scope. |

The main dependency chain is explicit: effective translation gives
`T^theta`; the existing unprimed construction gives `S_(T^theta)`; the fixed
PA identity/zero classes give inseparability. The lambda argument has a
different dependency: precompleteness gives inseparable classes, and
maximality would provide a terminating two-search decision procedure.

## Local findings and repairs

| Location | Issue | Editorial rationale | Recommended repair |
| --- | --- | --- | --- |
| §1, first paragraph | “On the same object” leaves the carrier unnamed, and “computational separator” is not defined locally. | This paragraph is the theorem whose scope organizes the note; its categorical conditions should be checkable in place. | Name the common object `P` and define a separator using complementary domains `c,d` on `P` with `I_T≤c` and `Z_T≤d`. |
| §2, final paragraph | “Covariant on interpretations under PA” precedes an explicit name for the objects of the source category. | The object assignment and compatible-interpretation condition are already present, but the reader must assemble the category. | Introduce objects `(T,theta)` and arrows `j:(T,theta)→(T',theta')` satisfying the displayed compatibility, then state the assignment to `S_(T^theta)` and its quotient functor on arrows. |
| §4, paragraph beginning “The uniform PA program-equivalence relation” | The symbol `R_PA` appears without its formula being displayed in this note. | The following contrast with sentence equivalence makes the precise relation important. | Before proving precompleteness, write `e R_PA f` iff `PA proves Eq(e,f)`, where `Eq` is the uniformly quantified graph-equality sentence defined in §2. |
| §3, final paragraph, “uniform program-identity requirements” | “Identity” can refer either to a program equation or to the distinguished identity morphism used elsewhere. | The note relies on that distinction. | Replace with “uniform program-equation requirements” or, more explicitly, “the uniform program equations used in the `S_T` construction.” |
| §2, expanded source-category definition | General sentence translations must preserve provable equivalence for the stated compatibility condition to be closed under composition. | Translating a theorem whose shape is a biconditional does not alone identify the translation with a biconditional between the translated constituents. | Require preservation of provable equivalence explicitly. |

These are exposition repairs, not assertions that the displayed proofs
are false. The report does not propose weakening any translation,
consistency, or precompleteness hypothesis.

**Final disposition.** The revised note names `P`, defines a computational
separator, identifies theories with their theorem sets, specifies the
source category and its actual sentence-translation arrows, requires
preservation of provable equivalence, displays the definition of `R_PA`,
and uses “program-equation requirements.” All listed repairs are resolved.

## Replacement wording supplied during review

For the beginning of §1:

> Fix a computational category with restriction domains and finite domain
> joins, and an object `P`. For each consistent extension `T` of `B`, let
> `I_T,Z_T` be domains on `P` arising as the identity and zero fibers of its
> presentation. A computational separator is a pair of domains `c,d` on
> `P` with `c∧d=0`, `c∨d=1_P`, `I_T≤c`, and `Z_T≤d`.

The existing hypotheses and one-sentence proof can then follow.

For the interpretation paragraph in §2:

> Consider pairs `(T,theta)` satisfying the translation hypotheses above.
> An arrow from `(T,theta)` to `(T',theta')` is an effective interpretation
> `j:T→T'` for which `j theta` and `theta'` are provably equivalent in `T'`
> on arithmetic sentences. Such an interpretation gives
> `T^theta⊆(T')^theta'`. Assign `(T,theta)` to `S_(T^theta)` and `j` to the
> quotient functor that fixes numerical types and program representatives.
> Identity interpretations and composition give identity functors and
> composite quotient functors, respectively.

For the beginning of the program-equivalence paragraph in §4:

> Put `e R_PA f` if and only if `PA proves Eq(e,f)`, with `Eq` the uniform
> graph-equality sentence from §2. This relation is precomplete.

The existing finite-computation argument then supplies the proof.

## Definition, notation, and terminology audit

- The translation is an effective map on arithmetic sentences. Its
  negation, falsum, and deduction properties are stated before `T^theta`
  is defined. Enumeration is correctly described without presuming an
  effective inverse translation.
- Equality in `S_(T^theta)` remains one uniform proof of a translated
  graph-equality sentence. The exposition does not introduce pointwise
  provable equality of program behavior.
- The category assignments and quotient-arrow assignments are explicit.
  The revised source category has pairs `(T,theta)` as objects and actual
  effective sentence translations preserving deduction and provable
  equivalence as arrows. Its compatibility law, identities, and
  composition are stated in one place.
- **Turing morphism** is used for the categorical universal computation
  structure. The note does not use “Turing compiler.” The numerical
  parameter-theorem argument asserts the existence of a total recursive
  map, without asserting a categorical operation on all arrows.
- The numerical and categorical formulations of precompleteness are
  distinguished. The partial pairing's restriction is stated, and the
  upward-closure argument specifies both inequalities needed for equality.
- The numerical inseparability lemma does not presume that its equivalence
  classes are c.e.; that additional conclusion is stated under the extra
  hypothesis that the relation is c.e.
- Program equivalence and equivalence of arithmetic sentences are kept
  separate. This distinction is substantive and should remain.
- The HA paragraph distinguishes syntactic completeness from an excluded
  middle schema. The lambda paragraph states the equational maximality
  consequence without introducing an arithmetic negation operation.
- The lambda application names its ambient computational category and
  distinguishes `K,K_*` from categorical identity and zero. This identifies
  the actual reach of the example and should remain.

## Scope

The complete supplied Markdown note was read. The source citations were
inspected as citations and their roles in the argument were identified;
the underlying arithmetic, set-theoretic, dominical, and lambda-calculus
papers were not independently reread for this editorial task. Those
mathematical and historical checks require the separate source and
mathematical reviews. No PDF was created or rendered, and no Lean
development was run. The note itself was not edited by this reviewer.

The complete revised note was reread, followed by a check of the final
equivalence-preservation and program-equation wording changes. Its final
inspected SHA-256 hash is
`0fc1c4248cefb5d2acb231c1f7a17ef211a0df01ae6e5f787cff89474063ae15`.
