# Version 29 citation audit: syntax, logic and initiality

VERSION29 frozen main paper only; no separate note or earlier revision; 9 keys, every one of 11 citation uses.

All nine works exist. All eleven citation uses have full primary-text support; one is a supported adaptation rather than the source’s literal axiom form. No invented reference, wrong claim or wrong locator was established. The CUP reissue date needs bibliographic qualification. No manuscript files were edited.

## Findings requiring distinction

1. **HP date precision.** The CUP frontmatter is ©2016, but its catalog dates print publication to 2 March 2017 and online publication to 24 March 2017. Prefer “Cambridge University Press, 2017 (©2016; reissue of the Springer text, originally 1993)” or explicitly label 2016 as the copyright year. This is a metadata qualification, not an invented book.
2. **HH equality adaptation.** §3.1 prints universally quantified variable reflexivity/substitutivity; v29 uses all-term versions with admissibility restrictions. The broad attribution to equality principles is supported. For exactness, identify these as term-instantiated forms; they should not be described as verbatim source axioms.
3. **Versions read.** Complete author versions were used for Goguen–Burstall and Gabbay–Pitts. Their section/theorem numbers support the citations. Their draft pages are not the publisher’s final pages. Official publisher records independently verify the publication metadata.

## Every citation use

| Key | V29 file and line | Locator | Status |
|---|---|---|---|
| GTWW | `appendices/a-syntax-and-theories.tex:163` | Section 2 | verified |
| GoguenBurstall | `appendices/a-syntax-and-theories.tex:164` | Section 4 | verified |
| FPT | `appendices/a-syntax-and-theories.tex:170` | Sections 2--4 | verified |
| GabbayPitts | `appendices/a-syntax-and-theories.tex:171` | Section 6 | verified |
| Katsumata | `appendices/a-syntax-and-theories.tex:172` | Section 2, Example 1(3) | verified |
| GabbayPitts | `appendices/a-syntax-and-theories.tex:300` | proof of Corollary 6.7 | verified |
| Aczel | `appendices/a-syntax-and-theories.tex:419` | Propositions 1.1.4 and 1.4.5 | verified |
| Wissmann | `appendices/a-syntax-and-theories.tex:469` | Lemma 3.6 | verified |
| HP | `appendices/a-syntax-and-theories.tex:509` | Section 0.10 | verified |
| HH | `appendices/a-syntax-and-theories.tex:522` | Sections 2.11--2.12 | verified |
| HH | `appendices/a-syntax-and-theories.tex:524` | Section 3.1 | verified_with_adaptation |

### GTWW — appendices/a-syntax-and-theories.tex:163

**Source location:** Section 2, pp.70–73, especially Proposition 2.1 and its following construction pp.71–72 (PDF pp.3–6).

Section 2 constructs the initial algebra for a many-sorted signature and identifies each carrier with well-formed expressions of that sort. Its constructor and unique-decomposition discussion supports the raw abstract-syntax attribution. This is ordinary many-sorted syntax, not by itself a treatment of capture avoidance or alpha equivalence. V29 correctly cites separate binding sources and separately assumes initiality stable under parameters in its category D.

**Correction:** None.

**Evidence:** <https://fldit-www.cs.tu-dortmund.de/~peter/IniAlg.pdf>

### GoguenBurstall — appendices/a-syntax-and-theories.tex:164

**Source location:** Section 4 “Parchments”, author report pp.15–16 (PDF pp.16–17); Section 4.1 pp.18–19 gives the equational example.

The actual text describes a syntactic signature whose sorts include terms and sentences, with constructors for those sorts and the language as the initial algebra. It describes the signature-indexed Lang functor and points to first-order, equational and Horn logic. This exactly supports the stated attribution; it does not supply v29’s internal, parameter-stable construction. The full primary author report was read; publisher metadata independently identifies the 1986 chapter. The report has different pagination from the published pp.313–333, but the cited section number agrees.

**Correction:** None.

**Evidence:** <https://www.lfcs.inf.ed.ac.uk/reports/86/ECS-LFCS-86-10/ECS-LFCS-86-10.pdf>; <https://link.springer.com/chapter/10.1007/3-540-17162-2_131>

### FPT — appendices/a-syntax-and-theories.tex:170

**Source location:** Sections 2–4, PDF pp.4–9: Theorem 2.1; Section 3 “Substitution”; Theorems 4.1–4.2.

Section 2 represents binding signatures on covariant presheaves and characterizes terms modulo alpha equivalence as the free signature algebra on variables. Section 3 develops single and simultaneous substitution; Section 4 characterizes the compatible algebra-plus-substitution model by initiality. The article’s terms are alpha classes/canonical nameless implementations, as v29 says. Its hypotheses and setting are not those of an arbitrary category D; v29 uses this as background and explicitly distinguishes its raw named syntax and admissibility subobject.

**Correction:** None.

**Evidence:** <https://www.dcs.ed.ac.uk/home/dt/FiorePlotkinTuri.pdf>

### GabbayPitts — appendices/a-syntax-and-theories.tex:171

**Source location:** Section 6, full author text pp.13–20: initial-algebra property (54), Theorem 6.2, Theorem 6.5, Corollary 6.7, Example 6.9.

Section 6 builds inductive FM-sets using atom abstraction, identifies the lambda syntax with alpha classes, obtains iteration/recursion from initiality, and constructs capture-avoiding substitution in Example 6.9. The setting requires finite support and freshness restrictions; v29 does not directly invoke that theorem for its category D and accurately distinguishes its raw named syntax.

**Correction:** None.

**Evidence:** <https://www.gabbay.org.uk/papers/newaas-jv.pdf>

### Katsumata — appendices/a-syntax-and-theories.tex:172

**Source location:** Section 2, Example 1(3), author PDF p.4; preceding typed-binding definition and immediately following initial-algebra characterization.

Example 1(3) gives the typed binding signature for first-order classical logic, including an existential quantifier, negation and disjunction. The preceding paragraph explicitly identifies alpha-equivalent terms, and the following paragraph characterizes syntax as an initial algebra in the category of presentation models. The cited claim says only “a quantifier”, so existential rather than universal causes no mismatch. The typed presheaf setting is not silently imported as a theorem about v29’s category D.

**Correction:** None.

**Evidence:** <https://www.kurims.kyoto-u.ac.jp/~sinya/paper/generalpre.pdf>

### GabbayPitts — appendices/a-syntax-and-theories.tex:300

**Source location:** Proof of Corollary 6.7, full author text p.17 (PDF p.17).

The proof replaces X by Lambda_alpha × X, applies initial-algebra iteration, and uses uniqueness to show the first projection recovers the original term. This is exactly the product-carrier trick being compared in v29. The source’s additional freshness condition is required for its binding theorem; the comparison borrows only this general recursion-from-iteration argument, with v29’s own explicitly defined slice algebra.

**Correction:** None.

**Evidence:** <https://www.gabbay.org.uk/papers/newaas-jv.pdf>

### Aczel — appendices/a-syntax-and-theories.tex:419

**Source location:** p.742 Proposition1.1.4 (PDFp4); pp747–748 Definitions1.4.3–1.4.4 and Proposition1.4.5 (PDFpp9–10)

Proposition1.1.4 characterizes the least rule-closed set by finite-length proofs for a finitary rule set. Proposition1.4.5 gives the well-founded proof-tree characterization; the preceding p747 discussion observes that finitary proof trees are finite. V29 expressly assumes a finite maximum arity N and presents the following slice-category construction as its own reformulation, so it does not falsely attribute that internal categorical generalization to Aczel.

**Correction:** None. Optional improve locator by adding pp.742,747–748.

**Evidence:** <https://lawrencecpaulson.github.io/papers/Aczel-Inductive-Defs.pdf>

### Wissmann — appendices/a-syntax-and-theories.tex:469

**Source location:** Lemma 3.6, p.31:10; proof p.31:11 (PDF pp.10–11), following coalgebra Lemma 3.3.

Lemma 3.6 states exactly that an (E,M) factorization system lifts to algebras for an endofunctor preserving E. In v29 the base is the regular slice D/F, with regular epimorphisms and monomorphisms. H preserves the left class by regular-epi stability under finite products/pullbacks and preservation of coequalizers by finite coproducts. The conclusion map is an H-algebra map to the terminal slice algebra, so factoring it is a valid instance. V29 supplies its own least-subobject proof rather than attributing that whole theorem to this lemma.

**Correction:** None.

**Evidence:** <https://lmcs.episciences.org/10014/pdf>

### HP — appendices/a-syntax-and-theories.tex:509

**Source location:** Preliminaries(a), numbered paragraph0.10, p7 (publisher excerpt PDFp3)

All three displayed propositional schemata in v29 match the three propositional axioms in 0.10 exactly, after replacing source implication notation. HP uses a conditional quantifier rule and treats equality as special axioms in0.11, but v29 attributes only the three propositional schemata to HP.

**Correction:** No substantive correction. Prefer “0.10, p.7” over “Section0.10” because 0.10 is a numbered paragraph.

**Evidence:** <https://assets.cambridge.org/97811071/68411/excerpt/9781107168411_excerpt.pdf>

### HH — appendices/a-syntax-and-theories.tex:522

**Source location:** §2.11 pp48–50; §2.12 p51 Axioms4–5 and generalization (PDFpp54–57)

Axioms4–5 exactly match universal instantiation and the displayed distribution axiom. §2.11 defines the free-for condition. V29 enforces the first restriction through Adm and the second through x absent from FV(phi). Source generalization is unrestricted for theorem proofs; v29 also restricts nonlogical axioms to sentences, so its generalization rule introduces no omitted open-assumption restriction.

**Correction:** None.

**Evidence:** <https://www.appstate.edu/~hirstjl/primer/hirst.pdf>

### HH — appendices/a-syntax-and-theories.tex:524

**Source location:** §3.1 pp64–65 Axioms6–7 and examples (PDFpp70–71)

The source gives universally quantified variable reflexivity and variable substitutivity, subject to free-for capture avoidance. It also illustrates replacing a variable by the constant2. V29 uses the corresponding all-term reflexivity and all-term formula-substitution schemata, with both substitutions admissible. The citation supports the stated equality principles; it does not literally print the exact term-parametrized schemata.

**Correction:** Optional precision: say “We use the term-instantiated form of the reflexivity and substitutivity principles in §3.1” or add a brief derivation. Do not call the displayed term schemata verbatim Hirst–Hirst axioms.

**Evidence:** <https://www.appstate.edu/~hirstjl/primer/hirst.pdf>

## Bibliography metadata (separate from claim verification)

### Aczel — verified

**authors:** Peter Aczel; **title:** An Introduction to Inductive Definitions; **container:** Handbook of Mathematical Logic; **editor:** Jon Barwise; **publisher:** North-Holland; **year:** 1977; **pages:** 739–782; **doi:** 10.1016/S0049-237X(08)71120-0

Chapter opening and ending verify page span and North-Holland1977; publisher confirms DOI. V29 supplies a text URL instead of DOI, which is valid.

**Correction:** None.

**Evidence:** <https://lawrencecpaulson.github.io/papers/Aczel-Inductive-Defs.pdf>; <https://www.sciencedirect.com/science/article/pii/S0049237X08711200>

### HP — verified_with_date_qualification

**authors:** Petr Hájek and Pavel Pudlák; **title:** Metamathematics of First-Order Arithmetic; **series:** Perspectives in Logic3; **publisher:** Cambridge University Press for Association for Symbolic Logic; **edition copyright:** 2016; **publication date print:** 2017-03-02; **publication date online:** 2017-03-24; **original copyright:** 1993; **springer paperback date:** 1998-03-17; **doi:** 10.1017/9781316717271; **pages:** xiv+460

V29’s2016 date matches the CUP frontmatter copyright, while current CUP catalog gives2017 publication. CUP frontmatter describes predecessor as1998; Springer catalog identifies first-edition copyright1993 and1998 softcover. Thus “2016 reissue of the1993 edition” is understandable but conflates copyright/publication and lacks version precision.

**Correction:** For exact publication metadata use “Cambridge University Press,2017 (©2016; reissue of the Springer text, originally1993)” or explicitly label2016 as copyright year.

**Evidence:** <https://assets.cambridge.org/97811071/68411/frontmatter/9781107168411_frontmatter.pdf>; <https://www.cambridge.org/core/books/metamathematics-of-firstorder-arithmetic/E72D370D90F316D86CB9D0927377A1A3>; <https://link.springer.com/book/9783540636489>

### HH — verified

**authors:** Holly P. Hirst and Jeffry L. Hirst; **title:** A Primer for Logic and Proof; **version:** 2015 Edition; **copyright:** 2002; **publisher:** author-hosted text; none asserted in v29; **doi:** none asserted

Full primary PDF titlepage agrees with v29 authors, title and version. The2002 copyright is not a contradiction of the expressly marked2015 edition.

**Correction:** None.

**Evidence:** <https://www.appstate.edu/~hirstjl/primer/hirst.pdf>

### GTWW — verified

**authors:** J. A. Goguen; J. W. Thatcher; E. G. Wagner; J. B. Wright; **title:** Initial Algebra Semantics and Continuous Algebras; **journal:** Journal of the ACM; **year:** 1977; **volume:** 24; **issue:** 1; **pages:** 68–95; **publisher:** ACM; **doi:** 10.1145/321992.321997

Published-article scan and DOI registrant metadata agree. The inaccessible ACM landing page did not prevent reading the complete article scan.

**Correction:** None.

**Evidence:** <https://research.ibm.com/publications/initial-algebra-semantics-and-continuous-algebras>; <https://api.crossref.org/works/10.1145/321992.321997>; <https://fldit-www.cs.tu-dortmund.de/~peter/IniAlg.pdf>

### GoguenBurstall — verified

**authors:** Joseph A. Goguen; R. M. Burstall; **title:** A study in the foundations of programming methodology: Specifications, institutions, charters and parchments; **container:** Category Theory and Computer Programming; **editors:** David Pitt; Samson Abramsky; Axel Poigné; David Rydeheard; **series:** Lecture Notes in Computer Science; **volume:** 240; **publisher:** Springer Berlin Heidelberg; **year:** 1986; **pages:** 313–333; **doi:** 10.1007/3-540-17162-2_131

All asserted metadata agree with Springer. “First online 2005” is retrospective digitization, not a contradiction of 1986 print publication. Full author report used for substantive check; final Springer pagination was not used as the evidence locator.

**Correction:** None.

**Evidence:** <https://link.springer.com/chapter/10.1007/3-540-17162-2_131>; <https://link.springer.com/book/10.1007/3-540-17162-2>; <https://www.lfcs.inf.ed.ac.uk/reports/86/ECS-LFCS-86-10/>

### FPT — verified

**authors:** Marcelo Fiore; Gordon Plotkin; Daniele Turi; **title:** Abstract syntax and variable binding; **container:** Proceedings of the Fourteenth Annual IEEE Symposium on Logic in Computer Science; **publisher:** IEEE Computer Society Press; **year:** 1999; **pages:** 193–202; **doi:** 10.1109/LICS.1999.782615

Conference archive and author bibliography verify the event/year/pages/publisher; IEEE verifies DOI. Author fulltext bears the subtitle “Extended Abstract”; omission of that subtitle matches the published IEEE title and is not an error.

**Correction:** None.

**Evidence:** <https://ieeexplore.ieee.org/abstract/document/782615/>; <https://lics.siglog.org/1999/FiorePlotkinTuri-AbstractSyntaxandVa.html>; <https://www.dcs.ed.ac.uk/home/dt/abstractsyn.html>

### GabbayPitts — verified

**authors:** Murdoch J. Gabbay; Andrew M. Pitts; **title:** A New Approach to Abstract Syntax with Variable Binding; **journal:** Formal Aspects of Computing; **volume:** 13; **issue:** 3–5; **year:** 2002; **pages:** 341–363; **historical publisher:** Springer-Verlag; **doi:** 10.1007/s001650200016

Publisher landing page and Pitts’s bibliography agree with v29. The author manuscript has provisional “2001, volume 0, pages 1–23” frontmatter. That provisional frontmatter is not evidence that the published 2002 citation is wrong; section/theorem numbering was checked in this complete author version. V29 omits issue 3–5 but does not assert a wrong issue.

**Correction:** None.

**Evidence:** <https://doi.org/10.1007/s001650200016>; <https://www.cl.cam.ac.uk/~amp12/papers/index.html>; <https://www.gabbay.org.uk/papers/newaas-jv.pdf>

### Katsumata — verified

**authors:** Shin-ya Katsumata; **title:** A Generalisation of Pre-logical Predicates to Simply Typed Formal Systems; **container:** Automata, Languages and Programming; **editors:** Josep Díaz; Juhani Karhumäki; Arto Lepistö; Donald Sannella; **series:** Lecture Notes in Computer Science; **volume:** 3142; **publisher:** Springer Berlin Heidelberg; **year:** 2004; **pages:** 831–845; **doi:** 10.1007/978-3-540-27836-8_70

Springer verifies all asserted metadata, including all four editors. Full author paper matches the cited section and example.

**Correction:** None.

**Evidence:** <https://link.springer.com/chapter/10.1007/978-3-540-27836-8_70>; <https://www.kurims.kyoto-u.ac.jp/~sinya/paper/generalpre.pdf>

### Wissmann — verified

**authors:** Thorsten Wißmann; **title:** Minimality Notions via Factorization Systems and Examples; **journal:** Logical Methods in Computer Science; **volume:** 18; **issue:** 3; **article:** 31; **year:** 2022; **pages:** 31:1–31:26; **publisher:** Logical Methods in Computer Science / Episciences; **doi:** 10.46298/lmcs-18(3:31)2022

Journal page and PDF verify metadata. Currently supplied journal PDF notes an update correcting Figure 10; Lemma 3.6 remains at the exact cited number. No version-specific claim about Figure 10 occurs in this use.

**Correction:** None.

**Evidence:** <https://lmcs.episciences.org/10014>; <https://lmcs.episciences.org/10014/pdf>

## Hypotheses and scope

The source distinction matters. GTWW supplies the ordinary many-sorted grammar/initial-algebra account. FPT, Gabbay–Pitts and Katsumata supply actual binding accounts with alpha equivalence, presheaf or finite-support structure, and substitution/freshness conditions. V29 explicitly distinguishes its raw named-variable syntax and admissibility subobject, and assumes its parameter-stable initial algebra. It does not claim that the background references establish that existence in arbitrary D.

For the initial derivation image, Wißmann’s Lemma 3.6 has exactly the required direction: preservation of the factorization system’s left class for algebras. The regular slice and H’s preservation argument make the use applicable. The least closed subobject conclusion is proved in v29.

For the Hilbert presentation, HH’s free-for and antecedent-variable restrictions are enforced by v29’s parameter subobjects. Its generalization occurs with sentence nonlogical axioms. The Aczel finite-proof attribution applies because the rules have finite maximum arity.

## Evidence cache and reproducibility

Downloaded PDFs, extracted text, scans/OCR for inaccessible text layers, DOI registrant JSON and download provenance are in `tmp/audit_v29/evidence/syntax/`. The JSON report records one row for every inventory use and separate metadata rows. Completeness was checked against `citation_inventory.json`: 9 keys and 11 uses.
