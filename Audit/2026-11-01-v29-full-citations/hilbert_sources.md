# V29 citation audit: Aczel, Hájek–Pudlák, Hirst–Hirst

Scope: frozen VERSION29 main paper only. All four citation uses were checked against actual primary fulltext at their locators. No invented reference or unsupported mathematical claim was found in this subset. There are two precision qualifications: CUP copyright/publication year, and the adapted equality schemata.

## Bibliography metadata

|Key|Result|Exact evidence and correction|
|---|---|---|
|Aczel|Verified|The chapter opens at739, ends782, names Peter Aczel, Handbook of Mathematical Logic, editor J.Barwise, North-Holland1977. Publisher confirms DOI10.1016/S0049-237X(08)71120-0. No correction.|
|HP|Date/version qualification|Authors/title/series/CUP/DOI all correct. Publisher frontmatter says this edition ©2016; CUP catalog says print2March2017, online24March2017. Springer records original©1993 and1998 paperback. Prefer publication2017 with ©2016 qualification; no basis to call the source invented.|
|HH|Verified|Primary titlepage explicitly says HollyP.Hirst and JeffryL.Hirst, A Primer for Logic and Proof,2015 Edition.2002 copyright does not invalidate the edition label. No publisher or DOI claimed.|

## Per-use findings

### Aczel — appendices/a-syntax-and-theories.tex:419 — verified

Source: [https://lawrencecpaulson.github.io/papers/Aczel-Inductive-Defs.pdf](https://lawrencecpaulson.github.io/papers/Aczel-Inductive-Defs.pdf). Location: p.742 Proposition1.1.4 (PDFp4); pp747–748 Definitions1.4.3–1.4.4 and Proposition1.4.5 (PDFpp9–10).

Proposition1.1.4 characterizes the least rule-closed set by finite-length proofs for a finitary rule set. Proposition1.4.5 gives the well-founded proof-tree characterization; the preceding p747 discussion observes that finitary proof trees are finite. V29 expressly assumes a finite maximum arity N and presents the following slice-category construction as its own reformulation, so it does not falsely attribute that internal categorical generalization to Aczel.

Correction: None. Optional improve locator by adding pp.742,747–748.

### HP — appendices/a-syntax-and-theories.tex:509 — verified

Source: [https://assets.cambridge.org/97811071/68411/excerpt/9781107168411_excerpt.pdf](https://assets.cambridge.org/97811071/68411/excerpt/9781107168411_excerpt.pdf). Location: Preliminaries(a), numbered paragraph0.10, p7 (publisher excerpt PDFp3).

All three displayed propositional schemata in v29 match the three propositional axioms in 0.10 exactly, after replacing source implication notation. HP uses a conditional quantifier rule and treats equality as special axioms in0.11, but v29 attributes only the three propositional schemata to HP.

Correction: No substantive correction. Prefer “0.10, p.7” over “Section0.10” because 0.10 is a numbered paragraph.

### HH — appendices/a-syntax-and-theories.tex:522 — verified

Source: [https://www.appstate.edu/~hirstjl/primer/hirst.pdf](https://www.appstate.edu/~hirstjl/primer/hirst.pdf). Location: §2.11 pp48–50; §2.12 p51 Axioms4–5 and generalization (PDFpp54–57).

Axioms4–5 exactly match universal instantiation and the displayed distribution axiom. §2.11 defines the free-for condition. V29 enforces the first restriction through Adm and the second through x absent from FV(phi). Source generalization is unrestricted for theorem proofs; v29 also restricts nonlogical axioms to sentences, so its generalization rule introduces no omitted open-assumption restriction.

Correction: None.

### HH — appendices/a-syntax-and-theories.tex:524 — verified_with_adaptation

Source: [https://www.appstate.edu/~hirstjl/primer/hirst.pdf](https://www.appstate.edu/~hirstjl/primer/hirst.pdf). Location: §3.1 pp64–65 Axioms6–7 and examples (PDFpp70–71).

The source gives universally quantified variable reflexivity and variable substitutivity, subject to free-for capture avoidance. It also illustrates replacing a variable by the constant2. V29 uses the corresponding all-term reflexivity and all-term formula-substitution schemata, with both substitutions admissible. The citation supports the stated equality principles; it does not literally print the exact term-parametrized schemata.

Correction: Optional precision: say “We use the term-instantiated form of the reflexivity and substitutivity principles in §3.1” or add a brief derivation. Do not call the displayed term schemata verbatim Hirst–Hirst axioms.

## Evidence and provenance

Downloaded and preserved Aczel’s full chapter; the full2015 Hirst–Hirst primary PDF; the CUP excerpt containing0.10; CUP frontmatter; and a publisher-supplied preview. Source URLs, byte counts and SHA256 checksums are in `tmp/audit_v29/evidence/syntax/hilbert_provenance.json`. Plaintext is alongside the PDFs. Reading was limited to the claimed points and context needed to check hypotheses; these conclusions do not claim a line-by-line review of the complete books.

The exact equality source differs from v29’s formulas: HH Axiom6 is universal variable reflexivity, while v29 adopts t=t for every term. HH Axiom7 is variable equality substitutivity, while v29 adopts a two-term substitution formula. These are standard corresponding derived/term-instantiated principles, and v29’s wording says only that equality is expressed by these principles. This is an attribution precision issue, not evidence of an incorrect equality scheme.
