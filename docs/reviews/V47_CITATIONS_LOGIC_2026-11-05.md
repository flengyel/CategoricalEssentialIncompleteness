# Citation audit: logic, syntax, Miller sequences, and cosheaves

The 17 references assigned to this audit support their attributed claims. No mandatory correction to their bibliographic data or mathematical attributions was found. Remove the Ramesh paragraph and its sole bibliography entry on relevance grounds: the paragraph accurately summarizes a parallel approach but states no relationship used by this paper. Retain the remaining references for the specific roles recorded below.

Audit date: 5 November 2026. Source tree: `manuscript/latex`, corresponding to repository head `fc47dd92e97373244f72bfe191456863e6de8e88`, with concurrent editorial changes. The inventory contains 21 citation occurrences for 17 keys before removal of Ramesh. Section names and labels below identify locations when editorial changes move line numbers.

## A. Hard blockers

None established by this citation subset. In particular, the Miller citation includes the paragraph after Theorem 6.3, which supplies the stronger equality at the same program index; citing the theorem alone would not identify that additional assertion as precisely.

## B. Major weaknesses

None established by this citation subset. Accuracy and relevance are separate: an accurate summary need not earn space in the introduction. Ramesh's sole paragraph is the removable case here.

## C. Citation-use audit

“Keep” means that the citation has a stated mathematical or attribution role, not that the manuscript imports every theorem of the source. Each source identifier links to the primary text or publisher record in the source ledger below.

| Key and manuscript location | Claim and source passage checked | Decision |
|---|---|---|
| `Miller2004`, Introduction, paragraph beginning with the sequence $a:\mathbb N\to[0,1]$ | Miller constructs the sequence used in the application. Theorem 6.3 and the following paragraph in [M1] give the construction and its stronger same-index property. | Keep: provenance of the principal external input. |
| `Miller2004`, § “Miller sequences and essential incompleteness”, opening | Exact locator “Theorem 6.3 and the following paragraph.” Lemma 6.2 and the proof of Theorem 6.3 explain the coordinate assigned to a program; the following paragraph states the additional property. | Keep the full locator, including the following paragraph. |
| `BauerHanson`, Introduction, countable Dedekind reals | [B1], Theorem 6.4, proves an epimorphism from the natural numbers to the Dedekind reals in the constructed parameterized realizability topos. Its proof uses the Miller sequence. | Keep; improve the bare citation to `Theorem 6.4`. |
| `BauerHanson`, Miller section, opening | [B1], §2.1, Definition 2.1, and Theorem 2.2, give binary representations of sequences and uniform computation from every representing oracle, with the same-index conclusion. | Keep: this is the particular representation convention used by the manuscript, not a duplicate of Miller's original presentation. |
| `Composition`, § “Syntactic recursion categories”, paragraph about primed systems | Corollary 2 in [L1] states that for consistent computably enumerable $T\supseteq\mathrm{PA}$, the proposed $S'_T$ composition does not define a category. The preceding theorem and proof construct two pointwise-provably equal representatives whose composites are inequivalent. | Keep: supports the distinction between the primed systems and the uniformly provable-equality construction. |
| `CurryCosheaves`, § “A recursion category from a three-point space”, opening and following definition | [C1], Definition 2.6, defines a cosheaf by the colimit over the nerve of a cover. In Set this is the displayed coequalizer of the coproducts over pairwise intersections and opens. The empty-cover clause gives the empty set. | Keep: definition and attribution are accurate. The article's cellular focus does not prevent its §2 general definition from applying here. |
| `Ramesh2023`, Introduction, sole paragraph | [R1], Definition 2.7 and the immediately following paragraph, specify an essentially algebraic extension of finite-limit categories with interpretation into an internal model. Introduction and Theorem 4.19 support the Löb and guarded-fixed-point summary. | Remove paragraph and entry: accurate, but the current paragraph makes no paper-specific comparison and supplies no construction or theorem used later. No new comparison should be invented merely to retain the citation. |
| `CockettLists`, Appendix A, “Categorical hypotheses and notation”, opening | The original scan [CL0], pp.5–7, was recovered and read. Lemma 2.2 and Definition 2.3 concern preservation of recursion by the product/pullback functor into a slice. Setting $B=1$ gives parameterized lists, as stated immediately after Definition 2.3. [MA1] independently corroborates the slice formulation. | Keep: exact antecedent for list parameterization. Remove the unrelated footnote about a gap in Lemma 5.6, as the syntax editor has done. That lemma is not the cited result. |
| `MaiettiLists`, same opening paragraph | [MA1], Definition 2.4 and the next paragraph, define parameterized list objects and state the equivalent preservation by pullback along the terminal map into a slice. | Keep: direct source for the slice formulation. |
| `GTWW`, Appendix A, “Terms, formulas, and free variables”, opening | [G1], §2, especially Proposition 2.1 and its following paragraphs, identifies the initial many-sorted algebra with well-formed expressions of each sort. The section also develops substitution through the free-algebra universal property. | Keep: source of the abstract-syntax method. |
| `GoguenBurstall`, same paragraph | [GB1], §4, printed pp.15–16 of the technical-report version, describes signatures whose sorts are syntactic classes and whose operations are constructors; the language is an initial algebra. The passage explicitly includes terms and sentences of logical languages. | Keep: explains the logical-language specialization of the preceding general initial-algebra citation. |
| `FPT`, Appendix A, binding/substitution paragraph | [F1], §§2–4: the term presheaf identifies alpha-equivalent terms, Theorem 2.1 gives initiality, §3 develops substitution, and Theorems 4.1–4.2 give the initial monoid/substitution-algebra treatment. | Keep: comparison with binding-sensitive syntax. |
| `GabbayPitts`, same paragraph, §6 | [GP1], §6, particularly Theorem 6.2, characterizes syntax modulo bound-variable renaming as an initial algebra in FM-sets. | Keep: a distinct binding framework and the source subsequently used for the recursion construction. |
| `Katsumata`, same paragraph | [K1], §2, Example 1(3), explicitly gives a first-order signature with a quantifier; the surrounding text takes syntax modulo alpha-equivalence. | Keep: makes the comparison specific to first-order syntax. It is contextual attribution, not an existence theorem for the manuscript's named syntax in every regular category. |
| `GabbayPitts`, Appendix A, formula-substitution construction, “proof of Corollary 6.7” | [GP1], the proof of Corollary 6.7, uses a product carrier containing the original syntax and the recursive result. The first projection is the identity by initiality. This is the construction invoked in the manuscript. | Keep: precise methodological attribution, independently checked by OCR of the relevant author PDF page. |
| `Aczel`, Appendix A, finite derivations/generated closure paragraph | [A1], Proposition 1.1.4, characterizes closure by deductions; Proposition 1.4.5 gives the proof-tree formulation. Definitions 1.4.3–1.4.4 and the surrounding text identify finitary rules with finite proof trees. | Keep: source of the finite-derivation description. The categorical image argument is supplied by the manuscript itself. |
| `Wissmann`, Appendix A, image/initial-algebra argument | [W1], Lemma 3.6, states that a factorization system lifts to endofunctor algebras when the endofunctor preserves the left class. The source's statement and proof context match the use with regular epimorphisms and monomorphisms. | Keep: exact categorical proof tool. |
| `HP`, Appendix A, “First-order theories”, three propositional schemes | [H1], §0.10, printed p.7, gives exactly the three displayed propositional schemes, in the same orientation. The downloaded page image was visually checked. | Keep: identifies the chosen Hilbert presentation. |
| `HH`, same subsection, quantifier axioms | [HH1], §§2.11–2.12, define “free for” and give the instantiation and quantifier-distribution axioms with the stated freshness condition. | Keep: supports the named-variable side conditions. |
| `HH`, same subsection, equality | [HH1], §3.1, gives reflexivity and substitutivity. Its formal axioms use variables; the manuscript explicitly says that it uses these principles “with terms as parameters,” so it does not misquote the presentation. | Keep this qualification: the manuscript uses the corresponding term instances. |
| `Keisler`, § “Ultrapowers of the code interpretation”, opening | [KE1], Theorem 3.1, is Łoś's formula equivalence for ultraproducts. Applying it to a constant family gives the ultrapower case used here. The manuscript states its set-theoretic choice assumption. | Keep: direct proof input. |

## D. Bibliography and cross-section consistency

All 17 entries identify real works and match the metadata checked below. Issue numbers omitted in the manuscript are optional and do not make an entry inaccurate. Publisher online dates must not replace original publication years.

| Key | Metadata checked and source |
|---|---|
| `BauerHanson` | Andrej Bauer and James E. Hanson, *The Countable Reals*, arXiv:2404.01256v3, 1 April 2026. The manuscript's 2026 date correctly identifies v3 rather than the 2024 first submission. [B2] |
| `Miller2004` | Joseph S. Miller, *Degrees of unsolvability of continuous functions*, JSL 69(2) (2004), 555–584, DOI 10.2178/jsl/1082418543. [M2] |
| `CurryCosheaves` | Justin M. Curry, *Dualities between cellular sheaves and cosheaves*, JPAA 222(4) (2018), 966–993, DOI 10.1016/j.jpaa.2017.06.001. [C2] |
| `Composition` | Florian Lengyel, *Pointwise provable equality and the failure of composition*, 2026, arXiv:2609.25556. The primary repository manuscript read is version 37, dated 30 September 2026. [L1], [L2] |
| `Ramesh2023` | Sridhar Ramesh, *Introspective Theories and Geminal Categories*, Berkeley Ph.D. dissertation, 2023. Institutional record and thesis title page agree. [R1], [R2] |
| `Aczel` | Peter Aczel, *An introduction to inductive definitions*, in J. Barwise, ed., *Handbook of Mathematical Logic*, North-Holland, 1977, 739–782. Original chapter scan. [A1] |
| `HP` | Petr Hájek and Pavel Pudlák, *Metamathematics of First-Order Arithmetic*. Cambridge lists publication in 2017; Springer identifies the original work as ©1993 and the 1998 softcover as a later printing. Thus “2017 reissue … originally published in 1993” is accurate. The Cambridge preview's ©2016 and its reference to ©1998 do not overturn these publication dates. [H1]–[H3] |
| `HH` | Holly P. Hirst and Jeffry L. Hirst, *A Primer for Logic and Proof*, title page “2015 Edition.” Its earlier copyright date is not an edition-date error. [HH1] |
| `GTWW` | J. A. Goguen, J. W. Thatcher, E. G. Wagner, J. B. Wright, *Initial algebra semantics and continuous algebras*, JACM 24(1) (1977), 68–95, DOI 10.1145/321992.321997. Title page and publisher-deposited metadata agree. [G1], [G2] |
| `GoguenBurstall` | J. A. Goguen and R. M. Burstall, *A study in the foundations of programming methodology: Specifications, institutions, charters and parchments*, LNCS 240 (1986), 313–333; editors Pitt, Abramsky, Poigné, Rydeheard; DOI 10.1007/3-540-17162-2_131. The publisher's later digital date is not the original publication year. [GB1], [GB2] |
| `CockettLists` | J. R. B. Cockett, *List-arithmetic distributive categories: Locoi*, JPAA 66(1) (1990), 1–29, DOI 10.1016/0022-4049(90)90121-W. Original scan and publisher-deposited metadata were freshly checked. The terminal character in “Locoi” is a letter, not a digit. [CL0], [CL1] |
| `FPT` | M. Fiore, G. Plotkin, D. Turi, *Abstract syntax and variable binding*, LICS 1999, 193–202, IEEE Computer Society, DOI 10.1109/LICS.1999.782615. [F1], [F2] |
| `GabbayPitts` | M. J. Gabbay and A. M. Pitts, *A new approach to abstract syntax with variable binding*, FAC 13 (2002), 341–363, DOI 10.1007/s001650200016. The publisher gives 2002; an author bibliography's 2001 date should not replace it. [GP1], [GP2] |
| `Katsumata` | S.-y. Katsumata, *A generalisation of pre-logical predicates to simply typed formal systems*, LNCS 3142 (2004), 831–845; editors Díaz, Karhumäki, Lepistö, Sannella; DOI 10.1007/978-3-540-27836-8_70. [K1], [K2] |
| `MaiettiLists` | M. E. Maietti, *Joyal's arithmetic universe as list-arithmetic pretopos*, TAC 24(3) (2010), 39–83. Author text and journal version agree. [MA1], [MA2] |
| `Wissmann` | T. Wißmann, *Minimality notions via factorization systems and examples*, LMCS 18(3) (2022), article 31, 31:1–31:26, DOI 10.46298/LMCS-18(3:31)2022. [W1] |
| `Keisler` | H. J. Keisler, *The ultraproduct construction*, author's survey, 1 June 2010, as dated on the linked text. The entry accurately identifies this version. [KE1] |

The use of Cockett and Maietti is restricted to list objects. Neither sentence attributes existence or parameter stability of the manuscript's general many-sorted polynomial syntax algebras to those sources. The distinction between named syntax and syntax modulo alpha-equivalence is also explicit and supported by the cited binding papers.

## E. Editorial actions

1. Remove the isolated Ramesh paragraph and, after checking that no other use was added, its bibliography entry. Reason: relevance, not inaccuracy.
2. Add `Theorem 6.4` to the introductory Bauer–Hanson citation. Preserve the different, already precise locator in the Miller section.
3. Retain the other citations and their precise locators. Retain the equality qualification “with terms as parameters.”
4. Keep the unrelated Cockett Lemma 5.6 footnote deleted. It does not qualify Lemma 2.2 or Definition 2.3 and interrupts the definition of the hypotheses actually used.

## F. Verification record

Claim-bearing passages of all 17 assigned works were read in this audit, using original journal scans, author manuscripts, publisher previews, or the author's source repository. The original Cockett scan was recovered from the project's files after external retrieval failed. Its pp.5–7 define recursive objects, identify them with initial algebras for $B+A\times-$, define the functor $I_Y(X)=(X\times Y\to Y)$, and define parameterized recursion as preservation by that functor. The immediately following paragraph identifies $\operatorname{list}(A)=\operatorname{rec}(A,1)$ and $\operatorname{rec}(A,B)\cong\operatorname{list}(A)\times B$. These passages directly verify the manuscript's attribution. The earlier audit [CL2] records the original PDF's SHA-256 `498c616cde927654db68da87b0c838aced4e852a2199f3cb34e78fcf5ba146cc`; it is supplementary provenance, not a substitute for this reading.

For `Composition`, the arXiv record was located but its body could not be retrieved; the complete author repository source was read instead. Its theorem counter makes the cited corollary Corollary 2, and its statement exactly supports the manuscript use. Goguen–Burstall and Gabbay–Pitts were downloaded and their claim-bearing scanned pages OCR-read because browser text extraction failed. The Hájek–Pudlák page was downloaded, rendered, and visually read. These distinctions concern the audit trail; none establishes a mathematical defect in the cited claims.

### Primary source ledger

- [B1] Bauer–Hanson full text: https://arxiv.org/html/2404.01256v3
- [B2] Bauer–Hanson version record: https://arxiv.org/abs/2404.01256v3
- [M1] Miller author PDF: https://people.math.wisc.edu/~jsmiller8/Papers/continuous.pdf
- [M2] Miller publisher record: https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/degrees-of-unsolvability-of-continuous-functions/976A65405A0C4D3784C7739673AE4D8C
- [C1] Curry full text: https://arxiv.org/html/1607.06942v1
- [C2] Curry publisher record: https://www.sciencedirect.com/science/article/pii/S0022404917301226
- [L1] Lengyel author source: https://github.com/flengyel/FailureOfComposition/blob/main/manuscript/failure_of_composition_2026-09-30_v37.tex (retrieved blob `3027cd18bbf55b7881c41fa233007703e27c638a`)
- [L2] Lengyel arXiv record: https://arxiv.org/abs/2609.25556
- [R1] Ramesh thesis, primary authored text mirrored at nLab: https://ncatlab.org/nlab/files/Ramesh-IntrospectiveTheories.pdf
- [R2] Ramesh institutional record: https://escholarship.org/uc/item/3mn0c475
- [A1] Aczel original chapter scan: https://lawrencecpaulson.github.io/papers/Aczel-Inductive-Defs.pdf
- [H1] Hájek–Pudlák publisher-distributed preview: https://api.pageplace.de/preview/DT0400.9781316731734_A29755690/preview-9781316731734_A29755690.pdf
- [H2] Cambridge publication record: https://www.cambridge.org/core/books/metamathematics-of-first-order-arithmetic/E72D370D90F316D86CB9D0927377A1A3
- [H3] Springer original-publication record: https://link.springer.com/book/9783540636489
- [HH1] Hirst–Hirst authors' text: https://www.appstate.edu/~hirstjl/primer/hirst.pdf
- [G1] GTWW published scan: https://fldit-www.cs.tu-dortmund.de/~peter/IniAlg.pdf
- [G2] GTWW publisher-deposited record: https://api.crossref.org/works/10.1145/321992.321997
- [GB1] Goguen–Burstall institutional technical report: https://www.lfcs.inf.ed.ac.uk/reports/86/ECS-LFCS-86-10/ECS-LFCS-86-10.pdf
- [GB2] Goguen–Burstall publisher record: https://link.springer.com/chapter/10.1007/3-540-17162-2_131
- [CL0] Cockett original scan: https://chatgpt.com/library?file_id=libfile_8d546a1b270081919859264849eac48a&account_id=personal — `cockettListarithmeticDistributiveCategories1990.pdf`, 29 pages; read printed pp.1, 5–7.
- [CL1] Cockett publisher-deposited record: https://api.crossref.org/works/10.1016/0022-4049(90)90121-W
- [CL2] Earlier direct-PDF audit and provenance: https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/fc47dd92e97373244f72bfe191456863e6de8e88/Audit/2026-11-01-v29-full-citations/Cockett1990/primary_citation_check.md
- [F1] Fiore–Plotkin–Turi author PDF: https://www.dcs.ed.ac.uk/home/dt/FiorePlotkinTuri.pdf
- [F2] Turi's publication record: https://www.dcs.ed.ac.uk/home/dt/abstractsyn.html
- [GP1] Gabbay–Pitts author PDF: https://gabbay.org.uk/papers/newaas-jv.pdf
- [GP2] Gabbay–Pitts publisher record: https://doi.org/10.1007/s001650200016
- [K1] Katsumata author PDF: https://www.kurims.kyoto-u.ac.jp/~sinya/paper/generalpre.pdf
- [K2] Katsumata publisher record: https://link.springer.com/chapter/10.1007/978-3-540-27836-8_70
- [MA1] Maietti author PDF: https://www.math.unipd.it/~maietti/papers/jartacrev.pdf
- [MA2] Maietti journal PDF mirror: https://www.kurims.kyoto-u.ac.jp/EMIS/journals/TAC/volumes/24/3/24-03.pdf
- [W1] Wißmann journal PDF: https://lmcs.episciences.org/10014/pdf
- [KE1] Keisler author PDF: https://people.math.wisc.edu/~hkeisler/ultraproducts-web-final.pdf

Downloaded primary evidence and selected OCR/page images are in `citation-evidence/`, including `hajek-pudlak-preview.pdf`, `hajek-pudlak-p7.png`, `gabbay-pitts.pdf`, and `goguen-burstall.pdf`. No manuscript or bibliography file was edited by this audit agent.
