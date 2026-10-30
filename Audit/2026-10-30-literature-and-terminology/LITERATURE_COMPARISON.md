# Literature comparison

30 October 2026. External review of Florian Lengyel, *Local connectedness,
range functors, and essential incompleteness*, Version 3, 30 October 2026.
This report concerns the literature and the scope of the contribution; it
does not certify the complete manuscript or change its text. Categorical
statements below use **restriction idempotent** consistently, including
when the cited authors use the term *domain*.

The paper advances the Di Paola–Heller program by using its categorical
inseparability theorem in actual theorem/refutation and
essential-incompleteness arguments. The search found no independent
author using the local-connectedness method to prove recursive
inseparability. That historical observation is qualified: Florian
Lengyel's own public 2006 report already presents the method, and the
existence of inseparable restriction idempotents in the present
three-point example also follows from the theorem attributed to Lengyel
in Cockett's notes. A strict extension of applicability beyond that join
theorem has not been demonstrated.

## Checked results and their relationship to the paper

The following are mathematical restatements, with notation normalized;
they are not verbatim quotations.

| Source and checked location | Statement and hypotheses | Comparison |
| --- | --- | --- |
| Di Paola–Heller (1987), Propositions 7.5–7.7, pp. 617–618 | In their \(c^+\)-dominical setting, full categorical choice supplies sections of copairings. Compatible maps can then be combined, and a complemented restriction idempotent is the inverse image of a coproduct summand under a total map. | This supplies the switching map used in their inseparability proof. The present local-connectedness, weak-choice, and lifting assumptions provide a different sufficient mechanism for this step. |
| Di Paola–Heller, Theorem 8.15, pp. 625–626 | For a Turing morphism \(\tau:X\times X\rightharpoonup X+X\), the restriction idempotents of \((1_X+0_X)\tau\Delta_X\) and \((0_X+1_X)\tau\Delta_X\) are recursively inseparable in their \(c^+\)-dominical setting. | The canonical pair and Turing-morphism argument have this direct predecessor. The new contribution cannot be identified merely with constructing that pair. |
| Di Paola–Heller, Theorem 8.18, p. 626 onward | Their full-choice setting yields effective inseparability. | The present recursive-inseparability conclusion is not, by itself, a stronger conclusion than the earlier result. |
| Bernardi (1986), Theorem 2, p. 128; standing recursion-category assumptions in §3, p. 126 | For a precomplete equivalence relation in a \(c^+\)-dominical recursion category, every two nonempty disjoint unions of equivalence classes are inseparable. | Bernardi's proof uses totalization and a precomplete fixed-point theorem. It does not use local connectedness or a range functor. The present theorem produces a particular Turing pair, so it has not been shown to generalize Bernardi's entire conclusion. PA-provable equality of programs already occurs in his examples on p. 125. |
| Heller (1990), Lemma 8.2 and Proposition 8.4, p. 1264; Theorem 9.2, p. 1265 | Local connectedness supports closure of Turing developments under composition and the existence theorem for recursion categories. | This is a construction of the computational category. No inseparability or incompleteness application was found in the complete paper's OCR. |
| Cockett, March 2010 slides 33–34; *Categories and Computability*, §7.3, Theorem 7.8 | A nontrivial discrete Turing category with finite compatible joins has inseparable restriction idempotents. Cockett expressly attributes the theorem to **F. Lengyel**. | The proof builds the switch using joins and applies a Turing-morphism argument; it does not invoke local connectedness or an external range functor. This records uptake of Lengyel's work, not an independent predecessor to it. |
| Cockett, *Categories and Computability*, §7.5, Theorem 7.14 | A nontrivial Turing category with zero and the specified provability predicate has a predicate on the terminal object distinct from zero and identity. | The provability predicate concerns the extensional ordering of programs represented by global points. The conclusion does not itself establish essential incompleteness of every consistent extension of a presented theory. |
| Cockett–Lack (2007), *Restriction Categories III*, Proposition 2.15 | Decisions can be characterized through restriction inverses of the appropriate copairings of restriction idempotents. | The switching section in the present argument is an instance of decision structure. The contribution concerns conditions producing and lifting it, not the invention of decisions. |
| Cockett–Guo–Hofstra (2012), *Range Categories I*, Theorem 4.14 | A small range category satisfying their range-agreement axiom RR.5 admits a faithful embedding into sets and partial maps preserving restrictions and ranges. | This statement does not assert preservation of coproducts, the required switch lifting, or compatibility with theory extension. It does not by itself replace the manuscript's specific model-family functor. |

Di Paola–Heller explicitly propose recursive inseparability of theorems
and refutable sentences as a formulation of generalized incompleteness
in their introduction, pp. 594–595. Their later discussion near p. 629
looks toward applications of the recursion-theoretic results to that
algebraization program. The present reductions into theorem and
refutation predicates, and their persistence under extension, therefore
address the program directly. Essential incompleteness of PA itself is
classical; the contribution is the categorical derivation and its
implemented nonnumerical application.

## Applicability: the distinction that matters

The three-point example lies outside the original dominical hypotheses.
The two nonzero restriction idempotents supported separately at its
endpoints have zero near-product. It also fails full categorical choice.
For example, in its ambient diagram category the componentwise
surjection

\[
q:(2\xleftarrow{1_2}2\longrightarrow1)
  \longrightarrow(1\longleftarrow2\longrightarrow1)
\]

has central component \(1_2\), but no natural section: the single value
chosen at the left endpoint would have to equal both central elements.
Restriction embeddings into the universal object transfer this
obstruction to the recursion category. These are deductions from the
manuscript's construction, not assertions found in the historical
sources.

The same example nevertheless falls under Cockett's join theorem.
The ambient partial-map category has partial inverses to diagonals,
compatible c.e. subdiagram unions give arrow joins, and the manuscript's
universal object gives the required Turing structure. Partial
invertibility of diagonals is discreteness, or semidecidable equality;
it does not require decidable equality. Fullness transfers the resulting
restriction idempotents on the universal object to the recursion
subcategory.

Thus the example establishes applicability beyond the original
dominical/full-choice results, but does not establish applicability
beyond the later discrete Turing-category theorem. Conversely, that
older theorem supplies existence of an inseparable pair; it does not
supply the manuscript's particular syntax, proof objects, reductions,
model-family functor, or essential-incompleteness application. The
present criterion assumes neither source discreteness nor source arrow
joins, but an example violating the older hypotheses is needed to prove
a strict extension of applicability.

## Lengyel's own prior work and adjacent literature

The institutional record identifies *Locally Connected Recursion
Categories* as CUNY technical report TR-2006011, published in 2006. Its
public abstract and indexed original PDF already describe
local-connectedness proofs of recursive inseparability, weak choice,
and transport through a range functor without near-product preservation.
This is earlier work by the present author. Cockett's attribution is
consistent with that provenance. The current explicit lifting condition
and the associated counterexample are substantive: the indexed earlier
statement alone does not verify the corrected theorem's complete
hypotheses or proof.

The author-provided abstract of *Six Classical Theorems in P-Recursion
Categories* also mentions connected restriction idempotents,
inseparability, and functors not preserving near-products. SSRN records
May 2004 as the date written and 14 May 2018 as the posting date. The
former is not evidence of public availability in 2004. Its full text
was not obtained, so no numbered theorem is attributed to it here.

Stefani's 1993 *A relativization mechanism in recursion categories*
concerns reducibility, relativization, and the semilattice of relative
categories. Its complete OCR and checked introduction/conclusion did
not reveal a local-connectedness proof of inseparability.

Other categorical incompleteness programs exist. Ramesh's 2023 thesis
*Introspective Theories and Geminal Categories* develops categorical
Löb principles and guarded recursion; Ikeda's 2026 thesis develops
related code structures and Gödel–Löb results. Savelyev's 2024
*Incompleteness theorems via Turing category* uses a concrete category
of Gödel encodings and categorical diagonalization. None of the
inspected material provided a competing local-connectedness proof of
recursive inseparability. These sources do preclude identifying the
contribution simply as the first categorical incompleteness theorem.

## Sources and access limits

- **Di Paola–Heller:** [publisher record](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/dominical-categories-recursion-theory-without-elements1-2/2E11506A81794B06EF34603881D79394). The original full PDF was examined, including the definitions of full and weak choice and the numbered results above.
- **Bernardi:** [author-uploaded full text](https://www.researchgate.net/publication/243062671_Precomplete_Equivalence_Relations_in_Dominical_Categories). The standing assumptions, Theorem 2, proof, and PA example were examined.
- **Heller:** [publisher record](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/an-existence-theorem-for-recursion-categories/5A24053486108F86AF005D88D63D40E8), DOI 10.2307/2274486. The relevant original pages and complete OCR were examined.
- **Cockett:** [author-hosted March 2010 slides](https://cspages.ucalgary.ca/~robin/talks/estonia-winter-2010/estonia-slides-4.pdf) and [author-hosted notes](https://cspages.ucalgary.ca/~robin/talks/estonia-winter-2010/estonia-notes.pdf). The currently hosted notes have title-page date **12 August 2014**, despite the directory name. The stated theorem locations were examined.
- **Cockett–Hofstra:** [*Introduction to Turing Categories* (2008), publisher record](https://www.sciencedirect.com/science/article/pii/S0168007208000948). The abstract and bibliographic record were checked; the complete published article was not independently inspected. The detailed theorem comparison above rests on Cockett's retrieved notes and slides.
- **Cockett–Lack:** [*Restriction Categories III* preprint](https://arxiv.org/pdf/math/0610500). Proposition 2.15 and the relevant decision structure were checked.
- **Cockett–Guo–Hofstra:** [official *Range Categories I* record](https://www.tac.mta.ca/tac/volumes/26/17/26-17abs.html) and [author-uploaded full text](https://www.researchgate.net/publication/265194097_Range_categories_I_General_theory). Theorem 4.14, pp. 440–442, was checked.
- **Rosolini:** [*Representation theorems for P-categories*, LNM 1348 (1988), pp. 307–315](https://link.springer.com/chapter/10.1007/BFb0081368). The chapter identity and introductory material were verified, but the complete text was unavailable. Removal of particular Di Paola–Heller assumptions is therefore not independently established in this report. The online 2006 date is not the print publication date.
- **Stefani:** [publisher record](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/relativization-mechanism-in-recursion-categories/D8511F8A71106E1F2CE2948613268E38). The original PDF and complete OCR were available.
- **Lengyel, 2006:** [CUNY institutional record](https://academicworks.cuny.edu/gc_cs_tr/277/) and [indexed original PDF](https://citeseerx.ist.psu.edu/document?doi=aa25ec78a22fd568f8410399adcf2fd62f8764b0&repid=rep1&type=pdf). The institutional metadata and indexed abstract/introduction/§4 were checked; direct PDF retrieval returned HTTP 403. The complete original proof was not independently verified.
- **Lengyel, *Six Classical Theorems*:** [author's SSRN abstract](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=3177577). Abstract and dates only; full text unavailable.
- **Ramesh:** [2023 thesis full text](https://ncatlab.org/nlab/files/Ramesh-IntrospectiveTheories.pdf). Abstract, structure, and targeted full-text searches were checked; this was not a complete proof audit.
- **Ikeda:** [author's 2026 thesis entry](https://ikeda.ac/pubs/ikeda2026/). Bibliographic information and abstract only.
- **Savelyev:** [arXiv record](https://arxiv.org/abs/2412.14084) and [full text](https://arxiv.org/html/2412.14084v1). The main statements, categorical setup, and relevant terminology were checked.

The search combined exact phrases and conceptual searches for local
connectedness, connected restriction idempotents, weak choice, range
functors, recursive inseparability, categorical precompleteness, and
categorical incompleteness. Negative text searches and incomplete
citation indexes cannot establish absolute priority. The supported
conclusion is a distinct local-connectedness and lifting method,
originating in Lengyel's own earlier work, now used in explicit
essential-incompleteness applications. No independent use of that
method was located; no strict extension beyond the compatible-join
theorem has been established.
