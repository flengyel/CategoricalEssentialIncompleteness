# Writing review: outline, terminology, and definition order

This author-side review consolidates PART_02–PART_07 for *Local connectedness, range functors, and essential incompleteness*, Version 5, 30 October 2026. The existing organization supports the argument: categorical definitions precede the model construction and lifting theorem; the applications state their constructions before the appendices prove the structural details. Retain that organization. The principal writing repairs concern explicit types, local hypothesis scope, and distinctions between functors, their values, and partial morphisms representing those values.

The finding identifiers and source-line anchors below refer to the immutable `build/sentence-review/baseline.tex`. The outline was checked against the current manuscript, including the revised headings “Evaluation functors” and “A universal object and a frame.” Several baseline findings have already prompted edits; this consolidation is not a final closure ledger or an overall disposition.

## Actual outline and dependencies

| Location and actual heading | Function and dependencies |
| --- | --- |
| Abstract | States source inseparability obtained through a locally connected target, the arithmetic application, and the propositional application. |
| 1. Introduction | Identifies the Di Paola–Heller problem and the source/target distinction; previews the main theorem and applications. |
| 1.1. Related work | Places the framework and inseparability results among Di Paola–Heller, Rosolini, Heller, Cockett–Lack, Cockett–Hofstra, Bernardi, and Montagna. |
| 2. Categorical preliminaries | Establishes the categorical vocabulary and conventions used throughout. |
| 2.1. Partial maps and restriction idempotents | Defines restrictions, totality, order, zeros, complements, inseparability, inverse image, range, and splitting; current text also defines restriction functors and restriction equivalence. |
| 2.2. Products, coproducts, and local connectedness | Defines restriction products/coproducts, range functors, local connectedness, partial monomorphisms, sections, and weak choice. Depends on 2.1. |
| 2.3. Recursion categories | Defines prodominical and isotypical categories and Turing morphisms. Depends on 2.1–2.2. |
| 3. The syntactic recursion category | Constructs $S_T$ from typed programs modulo uniformly provable graph equality and identifies its categorical operations. Depends on Section 2 and PA-formalized programming identities. |
| 4. Interpretation in models | Constructs $F_M:S_T\to\mathbf{Pfn}$ and proves preservation. Depends on Section 3's equality and graph identities. |
| 5. A faithful family and theory extension | Constructs the product target and faithful $F_T$, verifies target hypotheses, and defines $Q_{T,T'}$ and the model-family projection. Depends on Sections 2–4 and completeness/Löwenheim–Skolem. |
| 6. Switching and the local-connectedness theorem | Gives the main mechanism producing inseparable source restriction idempotents. |
| 6.1. The local-connectedness construction | Proves the connected summand alternative, constructs sections, and proves Theorem 6.3. Depends on Section 2; the theorem separately assumes source Turing universality and section lifting. |
| 6.2. A sufficient condition for lifting | Derives lifting from joins of morphisms with disjoint restriction idempotents. Depends on 6.1. |
| 6.3. Lifting in the syntactic category | Constructs selecting programs and obtains inseparability in $S_T$, stable under consistent theory extension. Depends on Sections 3–5 and 6.1. |
| 6.4. From inseparable restriction idempotents to incompleteness | Pulls a proposed theorem/refutation separator back along a total morphism. Depends on the supplied inseparable pair and explicit inverse-image inequalities. |
| 7. Essential incompleteness of arithmetic | Applies Theorem 6.3 in the classical recursion category, then uses finite PA proofs and theorem ranges to apply Corollary 6.7. |
| 7.1. Numeral instances and theory extension | Defines the numerical proof/refutation pairs and their functorial enlargement, then explains the effective role of numeral instances. Depends on Section 7's fixed pair and proof objects; consistency and c.e. scope must be local. |
| 8. A recursion category from a three-point space | Defines the space, cosheaves, $J$, $\mathcal E$, $\mathcal A$, $V$, a frame, and $\mathscr R_X$; states structural results proved in Appendix A. |
| 8.1. Local connectedness and lifting | Applies the main theorem to $\mathscr R_X\hookrightarrow\mathcal A$ and explains non-equivalence with the classical category. Depends on Section 8 and Appendix A's structural results. |
| 8.2. Evaluation functors | Defines $E_j$ and compares the set-valued observations; proves preservation and the special Turing property for components 1 and 2. Depends on Section 8 and Appendix A.4's chosen construction. |
| 8.3. Proof observations and extensions | Builds the propositional theory, defines its extensions, and proves their internal and numerical inseparability. Depends on 6.4, 8.1–8.2, and Appendix B's syntax/proof construction. |
| A. Construction of the nonnumerical recursion category | Supplies the structural proofs announced in Section 8. |
| A.1. Cosheaves and functor categories | Proves the cosheaf equivalence, preserves the product/subobject counterexample, and proves regularity and extensivity of $\mathcal E$. |
| A.2. Partial maps, ranges, and connected restriction idempotents | Establishes the restriction structure, weak choice, ranges, and local connectedness of $\mathcal A$. Depends on A.1. |
| A.3. A universal object and a frame | Constructs embeddings into $V$, the nonempty-word functor, and the three frame isomorphisms. Depends on the explicit components of $V$. |
| A.4. A Turing morphism | Constructs the partial evaluator and its parameterization, checking component domains and naturality. Depends on $V$, acceptable numbering, and chosen tuple codings. |
| A.5. The recursion category and its splitting | Assembles $\mathscr R_X$, proves the splitting equivalence, and establishes the subobject-count and equality counterexamples. Depends on A.1–A.4. |
| B. Finite syntax and proofs | Supplies the construction used in 8.3. |
| B.1. The syntax algebra | Constructs the formula functor and proves its polynomial algebra initial. Depends on $J$, $\mathcal E$, and $V$. |
| B.2. The proof object and its range | Constructs finite proofs, proves leastness of their conclusion subfunctor, and proves consistency by a finite valuation. Depends on B.1 and the disjoint restriction idempotents $a,b$. |
| C. Necessity of section lifting for inseparability | Constructs $\mathcal C_K$ and verifies that the main theorem fails without lifting, despite additional functor preservation properties. Depends on Theorem 6.3 and the distinction between ordinary and oracle computation. |
| References | Supplies the cited framework, antecedents, and supporting constructions. |

## Grouped comparison of all PART_02–PART_07 findings

“KLR 11,” “KLR 14,” and “KLR 17” refer to verified Section 1 advice on introducing variables, consistent notation, and unambiguous left-to-right reading. Applying that advice to categorical types is an editorial judgment. The requested terminology and explicit-functor requirements are independent user constraints.

| Findings and baseline locations | Difficulty | Source principle or independent rationale | Recommended repair |
| --- | --- | --- | --- |
| P02-01; 477–479 | “These idempotents” shortens the requested term. | Explicit user terminology constraint; not a mathematical error. | Use “These restriction idempotents.” |
| P03-01; 585–586 | “Both these restricted arrows” has a false reading. | KLR 14, 17; the report exhibits a small counterexample to that reading. | Name $(a+b)\theta\gamma$ and $(a+b)\theta'\gamma$ explicitly. |
| P03-02–03; 713–728 | Undeclared $c_M,c'_M$ and an unexplained change from coproduct injections to numerical coding terms. | KLR 11, 14; distinguish a morphism from its numerical implementation. | Use $F_M(c),F_M(c')$ and declare the code-level meaning of $i_jx$. |
| P03-04; 801–808, and 04-01; 918–949 | The generic extension correspondence and the local consistency hypothesis are implicit. | KLR 5, 11, 17; preserve the actual hypotheses and quantifiers. | State that represented extensions satisfy $t\ge t_0$; open 7.1 with a consistent c.e. $T\supseteq\mathrm{PA}$. |
| 04-02; 1011–1015, and C05-4; 1368–1386 | Values of a $J$-functor are confused with values of its associated cosheaf on opens. | Explicit functor source/target requirements; KLR 11, 17. | State the restriction functor and its component assignments; attribute evaluation at $X$ to the associated cosheaf. |
| 04-03; 1092–1095, and S06-02–03; 1567–1582 and later component arguments | Connectedness changes from a property of restriction idempotents to a property of subfunctors; positional component names are undeclared. | KLR 11, 14; preserve the type of a defined predicate and the explicit indexing category. | State connectedness of the partial identities; use component 0 and components $i=1,2$. |
| 04-04–06; 818–865 | Formal type/carrier notation drifts; $b$ has two roles; “tagged-input map” hides the section formula. | KLR 11, 14; independent explicit-typing requirement. | Retain $\omega$ for the formal type, name the parity isomorphism separately, and display the selecting section. |
| 04-07–08; 1034–1068, recurring in A.5 | “Partial category,” undeclared $\operatorname{Mono}$, and “formal objects” obscure the actual construction. | Established partial-map terminology; distinguish objects of the ambient category from expressions denoting them. | Say “partial-map category using all monomorphisms”; describe the objects obtained from $V$ by the stated operations. |
| C05-1–2; 1116–1185 | Extra names for evaluations and total morphisms; comparison with an unnamed forgetful functor. | Explicit user terminology constraint; KLR 11, 17; functor targets differ. | Use “Evaluation functors” and typed morphisms $p_y:H_i\to Y$; define $U:\mathcal K\to\mathbf{Pfn}$ and state $\Phi_i\cong UE_i$. |
| M05-1; 1251–1263 | Formula parameters are said to range over the functor $S$, not its component sets. | Explicit typing; KLR 11. | State the schemes at each $j$, with parameters in $S_j$, and specify the positive/negative atomic instances. |
| C05-3; 1236–1277, and P07-1, P07-3–5; 1937–2069 | “Split subfunctor,” “total natural map,” “three restrictions,” and “rule-closed” obscure the relevant category or operation. | KLR 11, 14, 17; distinguish total natural transformations in $\mathcal E$ from partial morphisms in $\mathcal A$. | Describe the subfunctor on which a partial identity is defined; use morphisms of $\mathcal E$, composites with coproduct injections, and closure under modus ponens. Say “polynomial functor” and “theory in classical propositional logic.” |
| C05-5; 1382–1405, and P07-6; 2110–2114 | Finite-set/slice conventions follow their use; halting notation is undeclared. | KLR 11; the strict first-use request, not a claim these conventional symbols are nonstandard. | Move existing conventions before use; include the two-element set, and add a short halting convention. |
| D05-1–2; 1148–1198, 1668–1734, and S06-06; 1902 | The evaluator's components, numbering choices, and abbreviated component morphism need a common declared convention. | KLR 11, 14; one constructed evaluator must use one fixed coding/numbering. | Introduce $\tau_j=E_j(\tau)$, explicitly reuse the construction's choices, and retain $r_1^V$ before its abbreviation. |
| S06-01, S06-04; 1486–1598, and P07-7; 2193–2219 | Partial morphism components and local variables/signatures are implicit. | KLR 11; explicit source and target declarations. | Name the representing morphism $D_f\to Z$ and its components; bind $Y,g,h$ locally; type $\tau_K$ and its parameter morphism $r$. |
| S06-05, S06-07; 1848–1904 | “Supported arrow” and “first truth value” replace the stated equations and coproduct property. | KLR 11, 17; avoid an unnecessary second terminology for an existing definition. | Use $f=dfe$ and refer directly to the first summand of $1+1$. |
| S06-08; 1064–1065, 1585, 1827 | The individual isomorphisms are called “frames.” | Primary-source correction recorded in PART_06: Heller, Section 3, defines the family with inverses as a frame. | Retain the established term, in the singular for the family, with its citation. |
| P07-2; 1933–1939 | “Fork” replaces the explicit functor description in the syntax construction. | Explicit user indexing requirement; KLR 11. | State $S:J\to\mathcal C_{\mathrm{rec}}$ with $S(j)=S_j$ and $S(0\to i)=\sigma_i$. |

The most consequential local repairs are the componentwise typing of axiom schemes, the category of the subfunctor representing a restriction idempotent, the distinction between $J$-evaluation and cosheaf evaluation, and the hypothesis scope in 7.1. The individual reports supply exact replacement wording. These repairs need no change of theorems, hypotheses, or the existing outline.

## Definition-order registry

| Notion or notation | Introduction and later role | Confirmed status or repair |
| --- | --- | --- |
| Composition; restriction idempotent; totality; order; inverse image; range and agreement | Section 2.1, before all constructions. | Adequate. Preserve “restriction idempotent” and ordinary uses of the domain of a partial function as distinct notions. |
| Restriction products/coproducts; diagonal/codiagonal; range functor; $\chi$ | Section 2.2, before Section 6. | Adequate. The range-functor definition explicitly states the paper's preservation convention. |
| Connectedness; partial monomorphism; section; weak choice | Section 2.2, before the target verifications and section construction. | Adequate definitions; later connected-subfunctor wording must refer back to the partial identities. |
| Prodominical, isotypical, Turing morphism, recursion category | Section 2.3. | Adequate; keep the established research vocabulary. |
| Typed index, $G_e$, $\equiv_T$, $[e]_T$, $[C]_T$, $R_e$ | Introduced in Section 3 in the order used. | Adequate. Typed indices are explicitly declared; $[C]_T$ is declared shorthand, not an unexplained second equality relation. |
| $X_M$, $F_M$, $\mathcal M_T$, $\mathcal D_T$, $F_T$, $Q_{T,T'}$, $\pi_{T,T'}$ | Sections 4–5 specify types, object/morphism actions, and the comparison square. | Adequate. The model product is indexed by a set; no undeclared inter-model morphisms are required. |
| Inseparable source pair, selecting section, and lift | Section 6 states all types and the lifting equation. | Adequate; retain the distinction between source universality and the target properties. Repair only the local notation listed above. |
| $\mathrm{Rec}$; arithmetic sentence/proof objects; $a,b,\theta,\nu,t_T$ | Section 7 introduces the category and constructions before the arithmetic corollary. | Adequate object introductions; restore the $\omega/\N$ convention and avoid reusing $b$ for the parity isomorphism. |
| $P_T,N_T,E_T,\kappa_n$; $\operatorname{Pair}(\mathrm{Rec})$ | Section 7.1 defines the sets and the pair category before their functorial use. | Adequate definitions; consistency must be in force before disjointness and bottom preservation. |
| Set-valued cosheaf; Sierpiński space; $X$; $J$ | Section 8 opening; the cosheaf axiom has a Curry citation. | Adequate definitions. Current text explicitly gives $J$'s objects and morphisms and distinguishes the two evaluation categories. |
| $\mathcal C_{\mathrm{rec}},\mathcal E$, component morphisms, c.e. subfunctor | Section 8 before $\mathcal A$ and $V$. | Adequate, explicit functor data and naturality equation. |
| $\mathcal A$, $V$, $V^\#$, frame, universal object, $\mathscr R_X$ | Section 8; Appendix A supplies announced proofs. | Objects and morphisms are introduced before the Turing claim. “Frame” is established vocabulary. Clarify the partial-map and generated-object conventions as listed. |
| $\mathcal K,E_j,\Phi_i,|e|_i,H_i$ | Section 8.2 introduces their data before use; $H_0$ is introduced locally in A.1. | Adequate basic introductions; explicitly type the forgetful comparison and evaluator components. |
| $P$, its initial algebra, syntax constructors, proof object, $c,t_0$ | Section 8.3 previews and Appendix B constructs them. | Initiality is explicitly stated. Give componentwise parameter types in the main text and clarify the subfunctor representing each restriction idempotent. |
| Regular epimorphism/category/image; kernel pair; extensivity | Appendix A.1 before the structural proposition. | Adequate; move the existing slice convention before its displayed use. |
| Total restriction embedding; word functor; acceptable numbering; $\simeq$ | Appendices A.3–A.4, before their named uses. | Explicitly introduced. The reports do not establish a definition-order defect merely because a term is specialized. Keep coding choices consistent with 8.2. |
| Decidable equality | Immediately before Proposition A.9; earlier use is a signposted preview. | Adequate. Use the defined first-summand condition in the proof, without adding “truth value.” |
| $S_j,\sigma_i,H_{k,j},\mathrm{Prf}_j,c_j,\rho_i$ | Appendix B's grammar, schemes, and proof construction precede their uses. | Adequate. Replace only the extra geometric/category terminology and clarify the initial $A,B$. |
| $K,W_a^K,\mathcal C_K,D_f,f_{e,a},p,A,p_A,s_A$ | Appendix C introduces the sets, category, and counterexample morphisms in order. | Adequate except the short halting convention and signatures of $\tau_K,r$. Preserve the ordinary/oracle distinction. |

## Source access and review limits

The verified supplied source is Knuth–Larrabee–Roberts, *Mathematical Writing*, Section 1, points 1–19 only (printed pages 1–3; PDF pages 3–5). The main review's request for the complete official Stanford PDF timed out. Later sections, including the contextual discussions of definition placement in Sections 4–5, were **not verified**. No recommendation here is attributed to those unread sections, and no claim of full-source compliance is made.

The individual PART reports were read, together with the current source and its changes from the baseline. Their findings are scoped author-side audits of terminology, definition order, and typing; they are not independent mathematical certification. The reports' differing severity labels are not combined into a journal recommendation. New compilation, final rendered-page verification, proof reconstruction, and renewed novelty or bibliographic research are outside this consolidation.

Preserve the substantive distinctions already doing mathematical work: a faithful functor may send an inseparable source pair to a separable target pair; internal inseparability alone does not give logical incompleteness; the associated cosheaf need not preserve componentwise products at $X$; and section lifting remains necessary in Appendix C's counterexample. Those passages should not be removed as merely defensive prose.
