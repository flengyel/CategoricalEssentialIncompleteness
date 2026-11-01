# Mathematical Writing review of the version-28 main-paper changes

The revised proof route is coherent: the comparison theorem and its lifted-separator corollary remain, a new corollary uses explicitly constructed total source conditionals, and the applications supply those conditionals. The moved local-connectedness criterion is not replaced by assurances about existence. Four local statement or typing repairs were identified and reported before closure. No shortening of unrelated proofs is recommended.

This is a review of the staged changes to *Logical consequence and essential incompleteness in recursion categories*, version 28, against the version-27 source in `tmp/move28/baseline`. Anchors below use source files and identifying labels; final PDF pagination was not yet available. The review applies the Mathematical Writing skill and the supplied Knuth–Larrabee–Roberts text, §1, particularly items 10–15 and 26. Source advice is distinguished from the author's additional requirements of explicit typing, one purpose per subsection, and avoidance of invented terminology.

## Outline of the changed argument

| Location | Function |
| --- | --- |
| Abstract and introduction opening | Update the announced hypothesis and references after moving the local-connectedness criterion. The full front-matter rewrite remains deferred. |
| §3.1, `thm:comparison` and `cor:separator` | Retain the comparison and the obstruction to a lifted complementary separator. |
| §3.2, `cor:source-conditionals` | Construct the target conditional from a total source morphism with the two stated restrictions, then apply `cor:separator`. |
| §3.2, `prop:disjoint-joins` | Retain the source construction of a total conditional from joins of disjoint-domain morphisms. |
| §6.1 | Apply the new corollary to the existing syntactic conditional and one-model interpretation. |
| Numerical §7.5 | Use the already displayed total recursive conditional. |
| Miller §§8.1–8.2 | Explain why one conditional program has the same output and domain for every representation; retain the separate compactness argument for the Turing morphism and the cut reduction. |
| Cosheaf §§9.1 and 9.3 | Construct the conditional by a copairing and an explicit natural inverse, and apply the new corollary internally and at the endpoints. |
| Appendix C | Retain the missing-lift example for the general comparison theorem. |
| Appendix D.1 | Apply the same source conditional coordinatewise and retain the theory-extension proof. |

## Findings and repairs

| Anchor | Difficulty in the first staged text | Principle or rationale | Repair |
| --- | --- | --- | --- |
| `appendices/c-section-lifting.tex`, `prop:missing-lift` | Removing “every hypothesis of Theorem 3.5” also removed the explicit assertion that `F` is a range functor. The proof still verifies it, but the statement no longer names a preservation property required by its comparison role. | Complete statement of the property being proved; independent mathematical rationale. | Write that `F` is a **faithful range functor**, then state the additional product and zero properties. |
| `sections/01-introduction.tex`, opening paragraph | The new corollary requires preservation of joins by **total** inverse images. The replacement opening retained an unrestricted statement about inverse images. | KLR §1, item 14: consistent notation and conventions; preserve the mathematical scope of the announced hypothesis. | “Total inverse images in the target preserve binary joins of restriction idempotents.” |
| `sections/03-sections-and-inseparability.tex`, opening paragraph | “In the applications, the required morphisms are constructed from complementary source restriction idempotents” was too broad. The direct arithmetic proof uses a partial proof-search lift and does not presume source complementarity. | KLR §1, items 10–12: connected exposition and a correct account of what follows; mathematical qualification. | Narrow the sentence to the total-conditionals criterion, rather than all applications of the general theorem. |
| `sections/04-miller-sequences.tex`, conditional paragraph after the definition of `K_p` | The paragraph started with complementary restriction idempotents on a numerical object without naming their category. The immediately preceding category is `K_p`, while representation independence is a property of the chosen morphisms in `E_a`. | KLR §1, item 11: introduce variables at their first use; explicit ambient typing is the author's additional requirement. | State `c,c':X ⇀ X` as complementary restriction idempotents **in `E_a`**. |

These findings are local repairs. They do not establish a false theorem, a missing realization, or a need for a global reorganization.

## Definitions, notation and proof detail

The new corollary specifies the total morphism `ell_c:U -> U+U` and the two restrictions that define its conditional behavior. The injections have declared types. Its proof names the source summand idempotents, invokes range agreement on the copairing `[c,c']`, gives both inverse-image identities, and constructs the typed target morphism using the canonical coproduct comparison. The final contradiction refers to the retained corollary with matching hypotheses. No appeal to local connectedness, weak choice, or an unspecified section is left in this proof.

The numerical case retains its displayed branch computation. The Miller case now explains termination and representation independence of the same branch program; the compactness/unanimity proof of the Turing morphism remains a distinct argument. The cosheaf case gives the copairing, its component inverses, the equation proving naturality of those inverses, and the final conditional copairing. These are useful complementary explanations in the sense of KLR §1, items 10–11; removing them to save lines would conceal the relevant construction.

The terms “range functor”, “restriction idempotent”, “coproduct injection”, “copairing”, “natural transformation”, and “conditional” are used with their stated categorical data. No new invented noun or adjective is needed. No drafting, audit, agent, or review commentary was found in the changed mathematical passages. The source/target distinctions between the recursion category, its target, and the functor category remain explicit at the affected uses.

## Organization and scope

No further outline change is recommended in this scoped review. The move leaves the main theorem and the application's direct constructions in one dependency chain. Proposition B.4 may remain as a property of the cosheaf category; the application no longer treats it as a prerequisite of the conditional construction.

The mathematical content outside the changed proof route was not re-proved by this writing review. In particular, the syntax/list/substitution initiality proofs, arithmetic code comparisons, ultrapower soundness, and the full bibliography were not newly certified. Existing front-matter issues outside the necessary factual changes remain reserved for the final revision. Compilation, final theorem numbering and rendering are the parent's separate checks. The revised standalone note has not yet been reviewed here.

**Disposition:** make the four local repairs above, then perform a narrow closure check on the resulting passages. No further compression or unrelated rewriting is called for.
