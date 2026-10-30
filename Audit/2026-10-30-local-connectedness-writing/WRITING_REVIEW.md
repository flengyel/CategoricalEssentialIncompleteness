# Mathematical-writing review of the renamed manuscript

The revision resolves the principal exposition defects recorded in
`INITIAL_WRITING_AUDIT.md`: the abstract explains its obstruction without
the earlier collection of undefined categorical labels, the Introduction
develops the requested literature comparison, and a preliminary section
defines the structures used in the technical arguments. The two further
first-use issues found during this review were reported before editing
and have been resolved. No consequential writing issue remains identified
in the reviewed source. This is an editorial conclusion, not a mathematical
certification or a claim of novelty.

Reviewed title: *Local connectedness, range functors, and essential
incompleteness*, dated 30 October 2026. Source:
`manuscript/local_connectedness_and_essential_incompleteness.tex`.
Reviewed SHA-256:
`1078044059fe239c27fdc82a9b69e7995e3b28c03d7310ff1ffb4164948d439f`.
The complete renamed source, including the abstract and bibliography, was
read in order. The final introductory and preliminary changes were reread.
This reviewer did not edit the mathematical manuscript.

The mathematical-writing plugin was applied using the supplied
Knuth–Larrabee–Roberts *Mathematical Writing* excerpt, Section 1,
points 1–19, printed pages 1–3 (PDF pages 3–5). The actual source is
Library file `libfile_53ef001c39508191895fe913d122fc16`; the local excerpt
is `loc_knuth_section1_excerpt.txt`. The verified principles used here are
self-contained theorem statements (5), connected prose (10), complementary
explanations and variables introduced at first use (11), reader motivation
(12), prose intelligible when formulas are skimmed (13), consistent
notation (14), and unambiguous reading order (17). The first-use table and
outline below are this review's methods, not a format attributed to the
book. The author's explicit requirement governs the abstract: specialized
terms must be explained there or omitted, even if a later definition would
normally suffice for the intended audience.

## Actual outline and dependencies

| Location | Function and principal content |
| --- | --- |
| Abstract | States the arithmetic conclusion, defines the classical inseparability obstruction, describes model interpretation and provable selection in plain language, and states the effective three-point application. |
| §1.1, Recursion categories and incompleteness | Introduces the Di Paola–Heller problem, explains restriction domains, places Rosolini's representation work in context, defines separators and essential incompleteness, and compares Bernardi's precomplete-equivalence approach. |
| §1.2, Local connectedness and comparison functors | Explains complementarity and local connectedness; distinguishes Heller's and corrected Lengyel-2004 existence results from the range-functor inseparability theorem; explains the role of lifting. |
| §1.3, Syntactic categories and the present applications | Introduces uniform provable program equality; distinguishes the valid unprimed categories from the primed systems with defective composition; previews model interpretation, effective arithmetic observations, and the three-point construction; supplies the roadmap. |
| §2.1, Partial maps and domains | Defines restriction structure, total arrows, orders, zero, complementary and inseparable domains, inverse images, ranges, splitting, and the restriction splitting. |
| §2.2, Products, coproducts, and local connectedness | Defines the product and coproduct structures and notation, range functors, connectedness, local connectedness, partial monomorphisms, sections, and weak choice. |
| §2.3, Recursion categories | Fixes prodominical and isotypical conventions and the typed Turing-morphism property before defining the adopted recursion-category convention. |
| §3, The syntactic recursion category | Defines numerical types and the uniform proof quotient; verifies composition, domains, ranges, products, coproducts, and the Turing morphism. |
| §4, Interpretation in models | Defines the object and arrow actions of the model functor and proves its preservation properties. |
| §5, A faithful family and theory extension | Constructs the product target, proves faithfulness and the target properties, and defines both directions in the commuting theory-extension square. |
| §6.1, The local-connectedness construction | Proves the connected-domain alternative and partial-injection section result; states the range-functor lifting theorem with its full hypotheses and proves inseparability. |
| §6.2, Lifting in the syntactic category | Builds one provably total program for each complementary source pair, identifies its interpretations with the required target section, and obtains the inseparable pair in every consistent `S_T`. |
| §7, Effective observations and essential incompleteness | Defines numerical observations, applies the local-connectedness theorem to `Rec → Pfn`, obtains a fixed numerical pair, embeds it into proof/refutation sets, and deduces arithmetic essential incompleteness. |
| §8, opening | Defines set-valued cosheaves, the three-point topology, computational fork diagrams, the partial-map category, the universal diagram, and the chosen frames. |
| §8.1, Local connectedness and lifting | Explains the connected finite subdiagrams, applies the inclusion into the split category, and gives the invariant witnessing nonnumericality. |
| §8.2, Endpoint functors | Defines the component functors on objects and spans, proves preservation and endpoint universality, and defines probes and observed domain carriers. |
| §8.3, Proof observations and extensions | Defines the observed inseparable pair, syntax and proof constructors, computational extensions, and the functor to numerical pairs; proves every consistent computational extension incomplete. |

The central question now precedes its preparation: how a categorical
inseparability theorem produces an obstruction to complete effective
theories. The principal dependencies are visible. The model-family theorem
uses §§2–4; the syntactic lifting result uses the target theorem and the
explicit selection program; arithmetic incompleteness additionally uses
finite computations and c.e. proof enumeration; the three-point result
uses the endpoint functors and the atomic proof inclusions. The latter two
effective steps are not attributed to faithfulness alone.

No further reorganization is proposed. The added preliminary section has
the specific purpose diagnosed in the initial audit, and the roadmap
matches the actual eight-section structure.

## Findings, repairs, and literature comparison

| Anchor | Issue or checked distinction | Governing principle or rationale | Final disposition |
| --- | --- | --- | --- |
| Abstract, selection sentence | An intermediate revision still used “complementary domains” without an abstract explanation. | Author's first-use requirement; Knuth §1, points 11–12. | Replaced by two cases that the theory proves disjoint and exhaustive. The program interpretation is stated directly. |
| §1.1, Rosolini and Bernardi paragraphs | “Dominical” occurred before its definition in §2.3. It was **late, not absent**. The literature comparison did not use the technical definition. | Reader expectations and economy; do not introduce an unused specialized distinction. | Removed the unnecessary adjective; Bernardi's conclusion remains explicitly conditional on his theorem's hypotheses. The unused weakly-total/dominical comparison paragraph was also removed. Bibliographic titles remain unchanged. |
| §§1.1–1.2 | The baseline omitted Rosolini, Heller's existence theorem, and Lengyel 2004 from the comparison. | Give each relevant antecedent a mathematical role; Knuth §1, point 12. | Each now has a stated role. Corrected faithful iteration functors are explicitly distinguished from the present range functors. |
| §1.3, unprimed and primed systems | A claimed locally connected syntactic system cannot be used if its composition fails to descend to equivalence classes. | Preserve substantive differences of hypotheses and constructions; distinguish a relation from a quotient category. | The paragraph names `S′` and `S′_T`, records the soundness qualification in DPM's claim, cites the composition obstruction, and contrasts the single uniform proof used by `S_T`. |
| §§5–6 | `S_T` and the product target `D_T` have different local-connectedness properties. | Consistent notation; avoid ambiguous attribution of a target property to a source. | The distinction is explicit at the theorem and again where it explains why target domains need not lift. |
| Theorem 6.3 and its proof | A lift whose image is total need not itself be total. | Preserve quantifiers and types rather than simplifying the claim. | The source lift is typed as partial, and the proof identifies precisely the totality it uses. |
| §7, final paragraph | Internal inseparability alone does not imply logical incompleteness. | Preserve an actual counterexample and a distinction needed for an inference. | `Th(N)` gives the mathematical reason for the separate effective step; this is substantive, not a defensive disclaimer. |
| §8.2–§8.3 | Partial domains, their numerical carriers, and the inverse image along negation are different objects. | Defined variables and consistent notation; Knuth §1, points 11 and 14. | `E_i(e)` is a partial identity, `|e|_i` is its carrier, and `ν* t` is explained as formulas whose negations lie in `t`. |

The final repair to the abstract reads:

> These functors preserve computation domains and images. Each map selecting
> between two cases proved disjoint and exhaustive by the theory is the
> interpretation of a program.

The Introduction is now a literature argument rather than a list of names.
Di Paola–Heller supplies the problem; Rosolini supplies the partial-map
framework and representation antecedent; Heller and Lengyel 2004 supply
the existence-theorem context and the role of local connectedness;
Montagna and Di Paola–Montagna supply the syntactic examples; the later
composition result rules out the primed construction for the stated
purpose; Bernardi supplies an established alternative approach to
inseparability. The current application is described without a universal
priority claim or a claim that every recursion category yields the same
logical conclusion.

## First-use and notation audit

Locations refer to the final source above. Standard category theory,
first-order logic, and elementary computability remain the intended
background; this table does not demand a dictionary definition of every
standard word. It does distinguish an informal introduction from a formal
definition and follows the stricter requirement for the abstract.

| Term or notation | First occurrence and explanation | Formal definition or construction | Status |
| --- | --- | --- | --- |
| Essential incompleteness | Abstract states that every consistent c.e. PA extension is incomplete. §1.1 names the general condition. | Arithmetic corollary in §7; the other extension class is fixed in §8.3. | Explained at first use. |
| Recursively inseparable pair | Abstract immediately explains disjoint c.e. sets and absence of a recursive separator. | Set-theoretic inequalities in §1.1; domain version in §2.1. | Explained at first use. |
| Recursion category | §1.1 describes the algebraic setting for partial computations. | §2.3 fixes the adopted convention after its constituent terms. | Acceptable introductory preview, absent from the abstract's specialized claims. |
| Restriction idempotent/domain | §1.1 immediately describes the partial identity retaining defined inputs. | §2.1 gives restriction axioms, totality, and domain order. | Explained before technical use. |
| Range and range functor | Ranges are described as images in §1.1; §1.2 gives the structures preserved by a range functor. | §2.1 gives the least receiving domain and agreement law; §2.2 gives the functor definition. | Defined before the construction of model functors. The abstract says domains and images. |
| Complemented and inseparable domains | §1.2 describes disjoint coverage and separation. | §2.1 states the domain equations and inequalities. | No unexplained complementary-domain terminology remains in the abstract. |
| Connected/local connected | §1.2 gives the decomposition criterion and detection of arrow equality. | §2.2 states both definitions with typed arrows. | Explained at the first substantive body use. |
| Lifting hypothesis | §1.2 identifies the particular selecting map and says it must be an image of a source arrow. | Theorem 6.3 types the source lift and states its equality with the target section. | The behavior precedes the technical equation. |
| Iteration functor | §1.2 describes the preserved operations in the corrected existence result. | Used only as an attributed literature comparison, not as an unstated hypothesis of the current theorem. | Sufficient local description for its role. |
| `S_T`, `S`, `S′_T`, `S′` | §1.3 describes uniform provable equality and separately describes pointwise provable equality. | §3 constructs only the valid unprimed quotient. | No unexplained `S_T` in the abstract; primed systems are not silently treated as categories. |
| Restriction category, split, restriction splitting | §2.1 introduces the axioms, typed splitting maps, and the objects/arrows of the splitting. | Same passage. | Before use in the model-family theorem. |
| Restriction products/coproducts; `Δ`, `∇`, `i_j` | §2.2 gives typed projections, injections, pairing/copairing, diagonal and codiagonal. | Same passage. | Before use in the Turing property and switching proof. |
| Partial monomorphism, section, weak choice | §2.2 gives typed tests and section equations, followed by the partial-function interpretation. | Same passage. | No longer introduced inside the application. |
| Prodominical; isotypical | §2.3 gives the zero-product condition and the all-objects-isomorphic condition. | Same passage. | Before the assertions about `S_T` and before the general theorem. |
| Turing morphism; total parameter map | §2.3 gives `τ:U×U⇀U`, the quantified input arrow, and a total `r:X→U` with its factorization. | Same passage. | Established terminology is retained; no “compiler” or “evaluator” substitutes. |
| Formal numerical type; `G_e` | §3 introduces the type grammar, codings, and the Σ₁ graph formula for a typed index. | Uniform quotient and its operations in §3. | Distinguishes program indices, graph formulas, and quotient arrows. |
| `D_T`, `F_T`, `Q`, projection | §5 constructs their objects/arrows and source/target categories before the theorem and square. | Same section. | Variance and both paths in the square are explicit. |
| Computational cosheaf | §1.3 describes the two-arrow diagrams with common source. | §8 defines the cosheaf condition, topology, diagram category, and computational carriers. | Abstract uses computable diagrams instead of the unexplained label. |
| Universal object; frames | §8 gives the retraction property and then the three specified computable isomorphisms. | Same passage, with the imported construction cited. | The named maps precede their use. |
| Endpoint evaluation; probe | §1.3 describes taking either target component after the diagram shape; §8.2 defines the actual functors and probes. | `E_j` on objects and spans; `Φ_i` on probes. | No endpoint language is left unexplained in the abstract. |
| Observed carrier `|e|_i` | §8.2 defines it as a numerical subset and identifies its partial identity. | Equation for probes and component evaluation. | Set and categorical-domain notation remain distinct. |
| Atom map and negation | §8.3 first gives the total polynomial and its initial algebra, then names the constructors `θ` and `ν`. | Typed maps and the explanation of `ν* t`. | Defined before the atomic inequalities and extension theorem. |
| Computational extension | Abstract states the c.e. subdiagram scope; §1.3 describes rule-closed computational domains. | §8.3 defines inclusion, rule closure, consistency and completeness before the theorem. | The conclusion concerns the specified effective class. |

The only uses of “dominical” remaining are in cited titles. “Prodominical”
is a different term and remains defined because it is a theorem hypothesis.
The manuscript does not use “abstraction” as unexplained terminology.

## Economy, mathematical boundaries, and checks

The complete-source pass assigned the prose to its mathematical functions:
problem and source comparison in §1; definitions in §2; constructions and
their verification in §§3–5; the section construction, theorem and
application in §6; effective consequences and the necessary boundary
example in §7; definitions, structural examples, observation and extension
proof in §8. No paragraph whose sole function is to narrate review or
reassure the reader about an unasserted claim was identified. The negative
statements retained have mathematical work to do: they distinguish the
primed and unprimed constructions, source and target connectedness,
lifting from arbitrary target separation, internal from effective
incompleteness, and endpoint from central universality.

The theorem statements retain their typed hypotheses. The source/target
extension square is a typed TikZ diagram and its commutativity is
explained. Functor actions, covariance, total/partial arrow conventions,
and syntax initiality are explicit. The review found no process commentary
in the mathematical source and no terminology drift to a “Turing compiler.”

Rendering checked by this reviewer: the 15-page contact sheet and readable
images of pages 1–3 from the build preceding the final removal of the two
introductory “dominical” labels and the unused comparison definition.
Those pages show the revised abstract, substantial three-subsection
Introduction, and beginning of the preliminaries. The final wording
changes were checked in source; the final rebuild and its page checks are
to be recorded in the separate verification report. This reviewer did not
run the compilation and does not claim inspection of a later PDF.

The existing mathematical proof verification is reused for unchanged
arguments. This review checks exposition and attribution scope; it does
not independently reverify every cited theorem in Rosolini, Heller,
Lengyel 2004 and its corrections, Bernardi, or the composition note.
Primary-source verification and the subsequent hostile-referee report
remain separate. No Lean formalization or Lean check is claimed.

The prioritized writing repairs from the initial audit and the two local
findings above are resolved in the recorded source. The next review is
the hostile mathematical review of that actual revised source, followed
by the final build and delivery checks.
