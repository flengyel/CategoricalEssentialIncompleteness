# Mathematical Writing review: version 41 revised passages

The revised second introductory paragraph now explains the categories and the distinction between the two representations of a sentence theory. The Miller extension sentence states its conclusion before its qualification. The terminology changes in the application sections distinguish restriction idempotents from subsets and partial-function domains. No further required prose repair remains in these checked passages.

## Scope and reading

I read the abstract, introduction, and Section 2.1 continuously, and inspected every other changed prose passage in the seven application/comparison section files against the frozen version 40 sources, using a freshly generated diff and its surrounding lines. After the subsequent instruction to retain the named operators, I reviewed the narrow changes in the introduction and Section 2.1. The other nine changed TeX files retain the reviewed hashes below; they were not subjected to another body review. The preamble change is version metadata. The first introductory paragraph is unchanged. This is a source-text review of the listed changes, not a new audit of all proofs or historical citations.

## Anchored findings and resolutions

| Anchor | Reader-facing assessment |
| --- | --- |
| Abstract, Miller sentence beginning “Every consistent extension is incomplete” | The conclusion comes before the condition. One fixed oracle program must semidecide the same axiom set with any binary representation as oracle; the wording preserves that scope without the former delayed predicate. |
| Introduction, second paragraph, “two representations of the same sentence theory” | The subobject and restriction idempotent are identified as distinct representations on the sentence object. The partial-function example supplies a familiar meaning for a restriction idempotent before the completion is introduced. Its explicit partial-function scope avoids assigning sets to objects of an arbitrary category. |
| Introduction, definitions of the three categories | The recursion category is named first. The restriction idempotent completion is then named, written as Split, and explained as splitting the restriction idempotents of that category. The category of total morphisms is named, written as Tot, and defined by retaining all objects and only total morphisms. Totality is immediately characterized by the restriction idempotent being the identity on the source. The operators now have names and meanings at first use. The phrase concerning total morphisms explicitly refers to the completed category, so its referent is unambiguous. |
| Introduction, sentence-conclusion image and partial-inverse paragraphs | The later partial-inverse hypothesis explains when the theory subobject also represents a restriction idempotent. Thus the introductory comparison does not silently identify a subobject with an endomorphism. Negation's inverse image is described as the restriction idempotent representing refutable sentences. |
| Introduction, comparison and inseparability paragraphs | Replacing categorical “domains” with the relevant restriction idempotents clarifies what is compared, separated, and pulled back. The direct reference “this pair” replaces the residual “the diagonal pair” after the earlier description changed, so no new label is introduced without an antecedent. |
| Introduction, syntactic and Miller realizations | The compact Tot-of-Split expressions are used after both operators have been named and explained in the second paragraph. They identify the two instances of the preceding construction without repeating its verbal description. The concrete Miller pair consists of partial identities on the displayed numerical subsets. |
| Section 2.1, restriction idempotents and total morphisms | Current terminology is defined first; the older use of “domains” is explicitly attributed to earlier recursion-category terminology. The category of total morphisms is named and defined with its objects as well as its morphisms. The restriction idempotent completion is also named before its formal description by objects and morphisms. The displayed splitting description supplies the detailed categorical definition. |
| Section 3, opening comparison paragraph | The target is a disjoint pair of restriction idempotents. The lifted partial morphism is described through its inverse images of the summand restriction idempotents; the resulting total morphism has zero inverse images of the target pair. The paragraph now names the categorical objects and equations it summarizes. |
| Section 8, parameterized syntax evaluation | “Total morphisms from” the displayed source objects replaces an ambiguous reference to “these source domains.” The preceding termination and parameter-fiber argument supplies the meaning of totality. |
| Sections 6 and 7.5, inverse-image laws | Binary joins of restriction idempotents replace unions of categorical “domains.” The numerical instance separately describes those joins as partial identities on unions of c.e. subsets, keeping the categorical and set-theoretic descriptions distinct. |
| Section 7.1, lemma title and incompleteness conclusion | The title names restriction idempotents. The conclusion says their interpreted join is not the identity, which states the categorical failure of completeness directly. |
| Section 7.4, displayed numerical function | The prose now says exactly that the function is defined on all of its source subset and has values in its target subset. This explains the two equations without using “source domain” for the categorical object. |
| Section 9, complementary idempotents and component evaluation | The total inclusions in the regular category and their splitting role in the partial-map category are distinguished. Membership searches refer to the component carriers. The refutation component is identified as a partial identity on the displayed inverse-image subset. These statements distinguish morphisms, split objects, and numerical subsets. |

The terminology repairs do not introduce replacement labels. Repetition of “restriction idempotent” is justified where the type determines an inference; concrete domains of ordinary partial functions remain appropriate in their explicit numerical context.

## KLR basis

The consulted source is Knuth, Larrabee, and Roberts, *Mathematical Writing*, Section 1, especially points 10–13 (printed pp. 2–3), 17 (p. 3), and 24 and 26 (p. 5). These passages support connected explanations, introducing meanings when needed, readable sentences, purposeful openings, and avoiding unnecessary jargon. The source does not prescribe a full proof outline for an abstract. The assessments above are applications to the current manuscript rather than additional rules attributed to KLR.

## Reviewed source identity

The following hashes identify all eleven TeX files changed from the frozen version 40 sources. In the introduction and Section 2.1 the continuous reading scope is specified above; in the seven other section files the review concerns the changed prose and local context, not every unchanged argument.

| File | SHA-256 |
| --- | --- |
| `abstract.tex` | `fb8d0a45696f2e196ca68783672b9940bdb7a278e5f670fab85d6aa76bc1ac3d` |
| `preamble.tex` | `1fa38b5ed11f9964b7093972a9c9798f81ce4f8eadc529db12f801da232b8faf` |
| `sections/01-introduction.tex` | `caff1941a920e17d77edc6b2d75bdfe468be7905955bc20173885a52d93d78d6` |
| `sections/02-categorical-preliminaries.tex` | `b63a65aa953669be4444610d2048b111f9c27ce10344cbae84bdd353acec8fdb` |
| `sections/03-sections-and-inseparability.tex` | `26175f2da0198a7710748e57083aa7490f0f1295fb5ebd5dfbc457ae8a5caae2` |
| `sections/04-miller-sequences.tex` | `9e24d7332b4c6cff89ca74b1c8c8cbb0b559bccd305e7142141c2c70aa6b9b83` |
| `sections/06-interpretation-in-models.tex` | `57be993cc95e618b0bf7ba9b9da652173145b4a64015717a349dbbc18e5bf122` |
| `sections/08-essential-incompleteness-of-arithmetic.tex` | `abf8ed7a20fb312bcc5e15ac3734f6943404d5fd99ff40ba654812bf6fe352e3` |
| `sections/08c-numerical-realization.tex` | `861e34e3a588c9e07ae1b6fbb622d6ff4568d22a6db9fcacd988f572445f4188` |
| `sections/08d-numerical-incompleteness.tex` | `1c50baab15f666707d5bda718abc6d2787b2427b098c52a3d42294d37457a6fc` |
| `sections/09-three-point-space.tex` | `7ab696ccfae2653c23abf16e6f4875cbefb44acbf983896bed72b6e2c6203bfb` |

No manuscript file was edited by this reviewer. Primary-source verification of the historical terminology is supplied separately by the mathematical review. Compilation, reference checks, and rendered-page inspection belong to the parent agent's validation record.
