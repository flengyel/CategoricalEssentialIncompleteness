# Final prose review of Version 2

Reviewed source:
`manuscript/essential_incompleteness_via_local_connectedness_v2.tex`.
SHA-256:
`cae09d2ed4cb0d9606eb7973ddfb4143fcd4736e7ccc3e0e8dd6c177248993b1`.
The source identifies itself as Version 2, dated 29 October 2026.

**Status:** the requested introduction shortening and the identified
antecedent, terminology, and typing repairs have been checked in this
snapshot. This is a prose-review result, not approval of the paper's
central claim. During this review the author reopened whether essential
incompleteness is being derived from the intended recursion-category
construction, rather than established by an additional numerical
argument. Publication and the abstract's account of that dependency
remain subject to that mathematical review.

## Method and scope

The mathematical-writing plugin governs this review, with the supplied
Knuth–Larrabee–Roberts *Mathematical Writing*, Section 1, points 1–19
(printed pages 1–3; PDF pages 3–5). The source excerpt was read directly.
The particular principles applied are self-contained statements (5),
connected explanatory prose (10), variables explained on introduction
(11), motivation and reader expectations (12), prose intelligible when
formulas are skimmed (13), consistent notation (14), and unambiguous
sentences (17). The author's stricter requirements for specialized
abstract terminology take precedence over a general allowance for an
introductory preview.

The initial outline and full baseline audit are preserved in `OUTLINE.md`
and `ANTECEDENT_REVIEW.md`. Every line of the revised mathematical source
was then read continuously, including the preamble, abstract, §§1–8,
Appendices A–C, and bibliography. The subsequent changed passages were
reread against the exact final hash above. An independent reader also
checked Appendices A–C. This report records the resulting prose checks;
it does not replace the separate mathematical referee report or the
existing verification of unchanged proofs. No mathematical source was
edited by this reviewer.

## Introduction economy and argument order

The Introduction now has seven paragraphs and approximately **634 prose
words**, compared with **1,174** in the baseline: a **46.0% reduction**
using the same approximate count, which excludes headings, citation and
reference commands, and inline mathematics. The reduction comes from
removing repeated previews and relocating detail, not deleting proofs.

Its actual progression is:

1. The Di Paola–Heller purpose, the separation obstruction, and essential
   incompleteness.
2. The relevant Rosolini, Heller, Lengyel, and Bernardi antecedents.
3. The range functor, locally connected target, selecting section, and
   exact lifting requirement.
4. The uniform syntactic category, the faithful family of model
   interpretations, and the exclusion of the pointwise quotient.
5. The separate numerical instance and finite arithmetic computations.
6. The explicitly specified three-point construction and its proposed
   incompleteness application.
7. The location of proofs and the counterexample with lifting omitted.

The original Lengyel result and its paired corrections are cited without
suggesting that failure to require near-product preservation is a new
correction. The fuller pointwise/uniform comparison is retained in §3;
the precompleteness comparison is retained at the end of §7. All
appendix proofs remain. The shortened introduction therefore preserves
the requested historical and mathematical subjects.

## Resolved findings

| Finding from the baseline or revision pass | Checked resolution |
| --- | --- |
| Undefined effective-diagram label | The abstract describes the carriers and arrows. The Introduction specifies c.e. subsets of finite numerical powers and partial recursive functions defined on their source carriers. Section 8 defines the category and its diagram category explicitly. |
| Conflation of numerical diagrams with arbitrary cosheaves | The associated set-valued cosheaf construction is distinguished from the numerical restrictions on objects and arrows. Appendix A retains the quotient pushout and the global-value qualification. |
| Unnamed coproduct comparison | Section 2 defines and types `χ_{X,Y}:FX+FY→F(X+Y)`; the lifting theorem and criterion use that comparison explicitly. |
| Unnamed or weakened lifting condition | The theorem names the total target section `s_c` and the source arrow `ℓ_c`, and states `Fℓ_c=χ_{U,U}s_c`. The prose does not infer source totality from target totality. |
| General product-preservation assumption | None was introduced. The added `X↦X×{0,1}` example explains why a range functor need not preserve products. Product preservation remains a separately stated property of particular functors. |
| Program index versus program arrow | The program-class notation is introduced. The selecting program is assigned index `e_s`; the graph is `G_{e_s}`, and its arrow is `s=[e_s]_T`. |
| Unspecified preserved operations | The theory-extension functor's preserved operations are listed explicitly. |
| Ambiguous inverse-image antecedent and free extension variable | The inverse images are those under `s_c`, and the extension `T′` is quantified in the corollary. |
| New informal reduction label | The identity morphism in `Pair(Rec)` is stated in place of the former shorthand. |
| Range object versus idempotent | Ranges are described as partial identities on image subdiagrams or regular images. The component carrier notation remains distinct from the domain idempotent. |
| Unbound endpoint index | The final application binds `i∈{1,2}`; the probe family also binds its index. |
| Carrier-total versus ambient-total recursion | Diagram morphisms and partial-arrow value maps are described as arrows of the stated numerical category. Genuinely total specialization functions retain the stronger description. |
| Singleton-probe antecedent | The singleton assertion concerns the nonempty components of the source probe. |
| Partial values described as having input domains | Range agreement now states definedness and equality of values at the selected input. |
| Unnamed semigroup extension and splitting comparison | The semigroup, its input map, its unique extension, and the direction of the classical splitting functor are explicit. |
| Unsupported transition to nonnumericality | The sentence now announces the nonnumericality argument before the count of subobjects. |
| Diagram denoted as though already a cosheaf | The global-value comparison refers to that value and its Cartesian square without introducing an undefined `H(X)`. |
| Ambiguous total-arrow antecedent in Appendix C | The category whose total arrows are being described is named. |
| Grammatical omission in the general theorem | The section introduction now reads “be the total section of”; its type and the following lifting equation agree. |

## Abstract and first-use check

The final abstract no longer lists unexplained range-functor, splitting,
local-connectedness, endpoint, or rule-closed-domain terminology. It
defines recursive inseparability, describes preservation of computation
domains and images, and states program selection between cases proved
disjoint and exhaustive. The effective diagrams and the effective class
of propositional extensions are described directly. The source/target
distinction between the syntactic category and the category of model
interpretations remains visible.

In the body, formal definitions occur before their technical use in the
proofs: restriction operations and domains, products and coproducts,
range functors and their comparison, connected domains, weak choice,
Turing morphisms, syntactic arrows, interpretation functors, the diagram
category, endpoint observations, syntax, and proof objects. Introductory
previews are accompanied by explanatory prose or an explicit reference
to the full statement. No additional consequential antecedent or invented
shorthand defect was found in the complete rereading.

## Reopened dependency: no claim of mathematical approval

The current §7 explicitly invokes the range-functor theorem again for
the inclusion of the classical recursion category into partial
functions. It then uses finite PA-provable computations to obtain the
proof/refutation inclusions. That is a separate route from the preceding
model-family construction for `S_T`. The Introduction now describes
this separation accurately, but merely making the separation explicit
does not establish that the paper meets the author's intended general
categorical goal.

In particular, the abstract's succession of the model-family theorem
and “Finite computations then give…” must be reconsidered after the
mathematical dependency is settled. This report does not certify a
deduction of essential incompleteness from the `S_T` construction,
completion of the Di Paola–Heller programme, or a theorem that every
complete extension necessarily supplies the required categorical
separator. The requested mathematical check must establish the relevant
implication and the exact extension class before those claims can be
approved. No wording-only change should be used to conceal that issue.

## Verification limits

The frozen source hash was checked directly. An earlier build of this
revision was inspected through extracted text, but this reviewer has not
visually inspected the final renamed Version 2 PDF. The root agent owns
the final build and rendering check. No Lean run, new formalization,
publication, or fresh independent proof certification is claimed here.
