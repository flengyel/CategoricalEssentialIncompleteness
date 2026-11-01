# VERSION29 citation audit: lists and Rosolini sources

Scope: the five delegated bibliography keys and all five uses in the frozen `local_connectedness` VERSION29 paper. The separate note and older versions were excluded. No manuscript edits were made. Audit date: 2026-11-01.

Four uses are verified from actual primary-source text. One use, `CockettLists`, remains **existence verified/fulltext unavailable**. No invented citation, bibliographic error, wrong locator, or substantive misattribution was established in this group.

## Bibliography metadata

| Key | Exact metadata verified | Evidence |
|---|---|---|
| CockettLists | J. R. B. Cockett, *List-arithmetic distributive categories: Locoi*, Journal of Pure and Applied Algebra 66(1) (1990), 1–29, DOI 10.1016/0022-4049(90)90121-W | Publisher-deposited Crossref record cached as `cockett_lists_crossref.json`; author-linked ResearchGate article record; Maietti bibliography [Coc90] |
| MaiettiLists | Maria Emilia Maietti, *Joyal's arithmetic universe as list-arithmetic pretopos*, Theory and Applications of Categories 24(3) (2010), 39–83 | [Journal page](https://tac.mta.ca/tac/volumes/24/3/24-03abs.html), [author text](https://www.math.unipd.it/~maietti/papers/jartacrev.pdf). Journal page supplies no DOI. |
| RosoliniThesis | G. Rosolini, *Continuity and effectiveness in topoi*, D.Phil. thesis, University of Oxford, 1986 | [Author-uploaded thesis](https://www.researchgate.net/profile/Giuseppe-Rosolini/publication/35103849_Continuity_and_effectiveness_in_topoi/links/57ef75b908ae886b89741067/Continuity-and-effectiveness-in-topoi.pdf), title page; Springer chapter references. Available PDF is the 1995 retypeset edition, 110 pages. |
| Rosolini | G. Rosolini, *Representation theorems for P-categories*, in F. Borceux (ed.), *Categorical Algebra and its Applications*, LNM 1348, Springer, Berlin/Heidelberg, 1988, 307–315, DOI 10.1007/BFb0081368 | [Publisher](https://link.springer.com/chapter/10.1007/BFb0081368), publisher-deposited Crossref record. Its 2006 online date is distinct from the 1988 print year. |
| RobinsonRosolini | E. Robinson and G. Rosolini, *Categories of partial maps*, Information and Computation 79(2) (1988), 95–130, DOI 10.1016/0890-5401(88)90034-X | [Publisher](https://www.sciencedirect.com/science/article/pii/089054018890034X), Crossref record, [author-uploaded published fulltext](https://www.researchgate.net/publication/319395054_Categories_of_partial_maps). The ResearchGate record's 1986 report label does not change the date of the uploaded journal article. |

All five bibliography entries match these data. Adding Rosolini's chapter DOI is optional.

## Every use

| Key and manuscript anchor | Status | Fulltext locator and assessment |
|---|---|---|
| CockettLists, `appendices/a-syntax-and-theories.tex:156` | Existence verified/fulltext unavailable | Original article could not be inspected. Its author-linked record explicitly offers no fulltext. Maietti's following paragraph after Definition 2.4 attributes precisely this recursive-object/pullback formulation to [Coc90], so the attribution is corroborated, but that does not replace checking Cockett's own article. No false claim established. |
| MaiettiLists, `appendices/a-syntax-and-theories.tex:157` | Verified | Definition 2.4 and immediately following paragraph, author PDF p4 (published p42). The definition gives parameterized list recursion, then states the equivalent recursive-object formulation preserved by pullback into slices. The manuscript has finite completeness through its regularity assumption and separately assumes initiality. It restricts the source attribution to lists. |
| RosoliniThesis, `sections/01-introduction.tex:109` | Verified | 1995 author edition: Chapter 2 opening p28; Definition 2.1.2 p29; Proposition 2.2.1 and the nonconverse examples p33. These establish the claimed generalization of dominical categories. |
| Rosolini, `sections/01-introduction.tex:109` | Verified | [Author-uploaded chapter](https://www.researchgate.net/publication/225697089_Representation_theorems_for_P-categories), opening p307; Definition 1.1 and Theorem 1.2 p308. The historical attribution is supported. The manuscript does not confuse embedding into partial maps with being an entire partial-map category. |
| RobinsonRosolini, `sections/05a-internal-syntax.tex:12` | Verified | Published pp108–109, the syntactic PA example immediately before Proposition 2.4. The source uses provably functional Sigma1 formulas modulo provable identity. The manuscript only cites this as a discussed presentation and proves its own construction for T; no transfer of the source's PA-specific proof is asserted. |

The complete machine-readable entries, including separate metadata records, evidence URLs, source locations, explanations, and correction fields, are in `categories_lists_rosolini.json`.

## Access limitations and provenance

The Cockett article was sought through DOI/publisher URLs, the author's linked publication profile, broad and exact-title web searches, and exact-title Library searches. No primary fulltext was obtained. ScienceDirect and Elsevier API routes returned an access page; Crossref metadata was successfully cached. This is an access limitation, not evidence of invention. To close that row, inspect an original scan; no manuscript correction follows merely from this limitation.

Rosolini's thesis was checked both through the public author-uploaded PDF and the user's Library copy `libfile_0a33ee9e09bc81918c351855b87977b4`. Its title page confirms Oxford despite conflicting third-party/ResearchGate catalog metadata naming Carnegie Mellon. The PDF's 1995 editorial note warns that the recovered typesetting may differ from the original, so page locators above explicitly name this edition.

Primary fulltext retrieval and metadata responses are cached under `tmp/audit_v29/evidence/categories/`: `lists_rosolini_retrieval.json`, `lists_rosolini_metadata_retrieval.json`, and the three `*_crossref.json` deposits. Failed publisher access responses are retained as `cockett_lists_publisher.txt` and `cockett_lists_api.txt`.
