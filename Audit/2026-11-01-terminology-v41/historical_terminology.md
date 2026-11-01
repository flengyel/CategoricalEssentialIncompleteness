# Historical terminology: restriction idempotents

The economical note needs only Cockett–Lack and Heller. The cited terminology was checked directly in their primary texts, rather than inferred from the manuscript or a secondary review.

Recommended wording after the definition of restriction idempotents:

> The morphisms $\bar f$ are idempotent and are called \emph{restriction idempotents} \cite[Section~2.1.1]{CockettLack}. These morphisms are called \emph{domains} in the earlier recursion-category terminology \cite[Section~5]{Heller}.

The second sentence is a historical terminology note. It does not retain “domain” as a second term used in the paper for these morphisms. “Domain” remains ordinary terminology for an actual partial function's set of defined inputs; Cockett–Lack also use the word for a morphism's source object. Neither use licenses treating an unspecified categorical object as the restriction idempotent itself.

## Direct primary-text evidence

| Source and printed locator | Verified content | Cached primary text |
| --- | --- | --- |
| Cockett–Lack, *Restriction categories I*, §2.1.1, p.227 | Calls a morphism equal to its restriction a restriction idempotent and identifies these as the morphisms of the form $\bar f$. Lemma2.1 gives their idempotence. | `tmp/audit_v29/evidence/categories/RestrictionI.txt`, lines236–239; PDF `RestrictionI.pdf`, page5. |
| Heller, *An existence theorem for recursion categories*, §5, p.1260 | Defines $\operatorname{dom}\phi:X\to X$ from the near product, calls it the domain of $\phi$, and describes the class of such endomorphisms as an inf-semilattice. | `tmp/audit_v29/evidence/recursion/Heller-ExistenceTheoremRecursion-1990.txt`, lines524–531; source PDF page10. |
| Di Paola–Heller, *Dominical categories*, Definition3.1, p.598 | Defines the domain of a morphism as an endomorphism of its source and expressly distinguishes it from a subobject. | `tmp/audit_v29/evidence/recursion/Cat Incompleteness/Paola-DominicalCategoriesRecursion-1987.txt`, lines286–295; source PDF page6. |
| Rosolini, *Representation theorems for P-categories*, §1, p.308 | Defines $\operatorname{dom}\phi:X\to X$ and explicitly follows Di Paola–Heller's terminology; in a partial-map category it is represented by $[m,m]$. | `tmp/frontmatter_v33/rosolini_preview.txt`, lines99–102; the supplied two-page preview. |
| Di Paola–Montagna, *Some properties of the syntactic p-recursion categories*, Definition1.3, p.645 | Uses “domain” for the derived endomorphism $\operatorname{dom}\phi$; Definition1.4 defines totality by its equality with the source identity. | `tmp/audit_v29/evidence/recursion/Paola-MontagnaPropertiesSyntacticpRecursion-1991.txt`, lines161–165. |

All cited works already have bibliography entries in the paper. Montagna's separate 1989 paper was not independently reread for this note; the joint Di Paola–Montagna source supplies the direct evidence if a longer author list is desired. A longer list is unnecessary for the proposed note.

## Split and total-category notation

Cockett–Lack introduce total morphisms and their category in §2.1.2, pp.227–228, using `Total(X)`. Their category obtained by splitting restriction idempotents is $K_r(X)$ in §2.3.3, pp.241–242. The manuscript's `Tot` and `Split` are therefore local notation and should be introduced with their definitions, rather than assumed to be familiar. No change to this notation was made by this reviewer.

Scope: a primary-text check of this short terminology note and its locators. No manuscript edits or broader citation audit were performed.
