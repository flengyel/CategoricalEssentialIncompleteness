# Mathematical-writing review

Reviewed manuscript: *Model interpretation of syntactic recursion categories*,
`manuscript/syntactic_model_range_functors.tex`, dated 30 October 2026.
The complete source was read before and after the expansion of Section 4.
This is an author-side editorial review, not a journal referee report or a
certification of mathematical correctness or novelty.

The manuscript states a concrete construction and keeps its categorical
roles distinct. The source is the syntactic category `S_T`; the locally
connected target is the product category `D_T` of model interpretations.
The effective comparison with classical recursion theory is a separate
construction requiring computably enumerable axioms. The enlarged Section 4
now supplies the local-connectedness argument and the range-functor theorem
needed for the application. No reorganization is required.

## Governing source consulted

Donald E. Knuth, Tracy Larrabee, and Paul M. Roberts, *Mathematical Writing*,
Section 1, points 1–19, was read from the supplied excerpt. The inspected
portion is printed pages 1–3, PDF pages 3–5, from Library file
`libfile_53ef001c39508191895fe913d122fc16`. The local excerpt is
`loc_knuth_section1_excerpt.txt` in the working directory.

The applicable verified guidance concerns self-contained theorem statements
(point 5), connected mathematical prose (10), defining variables at their
introduction (11), motivating the next step for the reader (12), prose that
remains intelligible when formulas are skimmed (13), consistent notation
(14), and unambiguous sentences (17). The report format and the checks of
source/target terminology below are supplementary editorial conventions;
they are not attributed to the book. Other portions of the book were not
read for this review.

## Actual outline and mathematical functions

| Location | Function |
| --- | --- |
| Title, metadata, and abstract | Identify the model-interpretation construction; distinguish the locally connected target from the non-locally-connected c.e. syntactic source; state the separate effective consequence. |
| §1, The syntactic recursion category | Fixes restriction notation and composition, defines the uniform program quotient, verifies composition and range laws, and states the Turing-morphism parameter property. |
| §2, Interpretation in models | Defines `F_M` on objects and arrows, including nonstandard trace interpretation, and proves preservation of the specified categorical structure. |
| §3, A faithful family and theory extension | Defines the model-indexed product and `F_T`, proves faithfulness and the target hypotheses, records the source's failure of local connectedness, and gives the strictly commuting extension square. |
| §4, opening | States what the local-connectedness theorem contributes and identifies lifting as the remaining application condition. |
| §4.1, The local-connectedness construction | Defines summand domains, proves the connected-domain alternative, obtains partial monicity and sections, and states and proves the general range-functor lifting theorem. |
| §4.2, Lifting in the syntactic category | Constructs one provably total switching program for each complementary source pair; proves its simultaneous interpretation in all models; applies the general theorem and explains why arbitrary target separators need not lift. |
| §5, Effective observations and essential incompleteness | Defines standard numeral observations, relates them to faithful interpretation, constructs the external proof/refutation pair, and gives the effective incompleteness argument and its non-effective boundary. |
| §6, The three-point alternative | Specifies the split computational ambient category and full recursion subcategory; verifies local connectedness through finite connected subdiagrams and obtains lifting through fullness. |
| Bibliography | Identifies the syntactic-category, local-connectedness, precompleteness, and three-point sources actually used or compared. |

Each paragraph of the revised source has a mathematical function: a
definition, construction, proof, application, comparison, or substantive
scope distinction. No paragraph whose sole role was review-process
narration was found. The abstract, source comments, and bibliography were
included in this pass.

## Findings and disposition

| Anchor | Actual issue or check | Source principle or editorial reason | Repair or status |
| --- | --- | --- | --- |
| §1, definition of range | “Receiving” initially appeared without its defining equation. | Point 11: define the notation and condition where introduced. | Repaired: a domain `r` receives `f` when `rf=f`. |
| §1, Turing-morphism display; §3, displayed assignments | The first supplied source contained malformed spacing/control sequences (`\\ Longrightarrow`, bare `qquad`, and bare `quad`). | These are concrete source defects affecting rendering. | Repaired in the revised source. Compilation and rendered-layout verification remain the responsibility of the separate build check. |
| Abstract and §3, source/target local connectedness | The application must not attribute the target's local connectedness to `S_T`. | Points 13–14: the prose and notation must preserve the distinction on which the construction depends. | Confirmed: local connectedness is assigned to `D_T`; the c.e. source statement is explicitly attributed to Di Paola–Montagna, Corollary 4.4. |
| §4.1, `prop:local-switch` and `thm:local-lifting` | The application previously depended on an external theorem for its central mechanism. | Points 5, 10, and 12: make the relevant hypotheses and proof dependencies available to the reader. | Repaired by the connected-domain lemma, section construction, and general lifting theorem with proof. |
| §4.1, final sentence of the lifting proof | Totality of the image of a lift must remain distinct from totality of the lift. | Point 14 and the explicit source/target conventions: these are different arrows in different categories. | Confirmed: the proof uses totality of `F ell_c=s_c`; it does not infer totality of `ell_c`. |
| §6, definition of `R_X` | The universal diagram underlying the subscript `X` was initially unnamed. | Point 11. | Repaired: `X` is explicitly introduced before `R_X`. |
| §3, definition of partial monomorphism | The types of `p,u,v` were initially implicit in the equation. | A local typing clarification makes the definition immediately checkable. | Repaired: the definition declares `p:X⇀Y` and quantifies over `u,v:W⇀X`. |
| §4.1, `prop:local-switch` statement | The type of its first section `s` was initially supplied only by its role and the subsequent proof. | Point 5, applied locally rather than by repeating all surrounding definitions. | Repaired: the statement declares the unique section `s:X⇀X+X`; the complementary case also gives its total type explicitly. |

All listed repairs are resolved. The final source also spells out the full
target hypotheses in the range-functor lifting theorem instead of relying
on a cross-reference to the section proposition. These local refinements
were reread; no unresolved editorial issue remains.

## Definitions, notation, and scope audit

- Composition, restriction domains, totality, domain order, inverse image,
  ranges, complementary domains, and inseparability are introduced before
  their use in the syntactic construction. The source/target objects of
  partial arrows are distinguished from their restriction domains.
- `S_T` uses a single uniformly quantified equality sentence. A primitive
  recursive trace test is distinguished from the existentially defined
  Sigma_1 output formula. No pointwise quotient is introduced.
- The universal computation structure is called a **Turing morphism**.
  Its defining property asserts the existence of a total parameter arrow
  for each indicated partial family. The manuscript does not introduce a
  “Turing compiler” or assert a functorial choice of parameters.
- The diagonal `Delta_X` is explicitly the total categorical diagonal.
  The effective pair in §5 is described through self-application rather
  than by using “diagonal” for an undeclared additional construction.
- `F_M`, `F_T`, `Q_(T,T')`, and the model-family projection have specified
  source and target categories and object and arrow actions. The extension
  square has matching endpoints, and the text explains why it commutes.
- Numerical elements of a model are distinguished from standard numerals.
  Model interpretation quantifies traces over the entire model. The
  faithfulness proof and the later standard-instance observation therefore
  do not silently assume arithmetic soundness.
- Local connectedness, splitness, partial monicity, and weak choice are
  introduced before the theorem establishing these properties in `D_T`.
  The independent source statement about c.e. `S_T` is explicitly separated.
- The proof of the section proposition distinguishes existence from
  totality: weak choice supplies the section; complementarity makes its
  restriction the identity. This distinction is retained in the general
  theorem and in both applications.
- The target's Boolean domain lattices and failure of target Turing
  universality explain why source inseparability and separability of its
  target image can coexist. These are substantive mathematical distinctions,
  not dispensable defensive disclaimers.
- Section 5 introduces the c.e. hypothesis at the point where proof
  enumeration is used. Its example of true arithmetic explains why the
  semantic representation by itself does not establish logical
  incompleteness.
- The three-point example uses the full inclusion into a split ambient
  category. It does not identify the isotypical source category with that
  split ambient category.

## Review scope and remaining verification

The complete revised LaTeX source was read, including the expanded local
connectedness argument, abstract, metadata, comments, and bibliography.
The supplied `LOCOct10f` Sections 4.1–4.5 and the stated portion of
*Mathematical Writing* were also read. This writing review does not claim
an independent recheck of every historical source or of the entire earlier
three-point construction; those checks belong to the mathematical and
source reports.

No manuscript edit was made by this reviewer. No PDF was compiled or
rendered during this review, and no Lean development was run. Compilation,
cross-reference resolution, and visual inspection of the rendered PDF
remain separate checks. No novelty claim is certified by this report.
