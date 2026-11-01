# Version 29: complete-source mathematical-writing review

The reviewed paper is **Florian Lengyel, “Logical consequence and essential incompleteness in recursion categories,” Version 29, 1 November 2026**. The frozen compiled source has been read in full before this diagnosis: all 22 TeX files, 6,862 lines, including the abstract, introduction, every section and nested input, all four appendices, and all 31 bibliography entries. No source has been edited.

The abstract and introduction remain reserved for the final revision under the user's instruction; O1 is deferred accordingly. The principal editorial opportunity is the introduction's first paragraph: its first sentence leads with a numbered corollary and a long list of machinery before stating the problem that machinery solves. The body is more legible than this opening suggests. It separates the comparison theorem, interpretation of theories, and three applications, and it usually explains which domain, graph, code, or carrier a formula denotes. I found **no confirmed required prose correction** arising from an absent major definition, an undeclared composition convention, an invented technical name, or editorial/process commentary in the compiled manuscript. The recommendations below are optional, local improvements; they are not mathematical objections or a certification of correctness.

## Governing source and method

I applied `c20/revise-mathematical-prose`, including its supplementary terminology and source-review instructions. I consulted the supplied Knuth–Larrabee–Roberts report in `tmp/review_sources/klr.pdf` and its text in `klr.txt`: §1 in full and §§4–5, with particular attention to the following verified advice. KLR printed pages 1–6 correspond to PDF pages 3–8; printed pages 9–13 correspond to PDF pages 11–15. I also inspected the actual PDF images of printed pages 2 and 9 to check the advice about theorem statements and contextual placement of definitions.

| Verified source advice | Application in this report |
|---|---|
| §1, point 5, printed p. 2: theorem statements should usually be self-contained. | Check each theorem's stated parameters and distinguish a locally explicit cross-reference from an unannounced hypothesis. I do not treat every cross-reference as a defect. |
| §1, points 10–11, printed p. 2: connect formulas with commentary; complementary explanations of definitions can aid understanding. | Preserve explanations of codes versus their interpretations, range versus regular image, and common oracle domains versus common output values. A repeated statement is not automatically redundant. |
| §1, points 12–13, printed p. 3: motivate the reader and make prose intelligible when formulas are skimmed. | Recommend a more informative first sentence and preserve the explanation preceding difficult constructions. |
| §1, points 14–15, printed p. 3: use notation consistently and avoid unnecessary indexing. | Track local changes of ambient category and the representative/class and code/value distinctions. |
| §1, point 17, printed p. 3: sentences should parse from left to right. | Prefer an explicit antecedent for “it” in the arithmetic corollary. |
| §1, point 24, printed p. 5: give particular care to the opening paragraph. | Recommend one replacement for the introduction's opening, without changing the organization or suppressing hypotheses in the later theorem statements. |
| §1, point 26, printed pp. 5–6: avoid unnecessary jargon and long noun strings. | Retain technical terms with a mathematical role; do not invent substitute names for familiar constructions. |
| §4, printed p. 9, and §5, printed p. 12: definition placement is contextual; definitions can be delayed if little is withheld, but symbols should be explained near use. | Accept the introduction's previews and the body's explicit references to Appendix A. Do not demand that this research paper define elementary background before every preview. |

The paragraph inventory and report organization are the skill's editorial workflow, not a format prescribed by KLR. The no-process-prose, exact typing, and economy checks also include the skill's supplementary requirements; they are not attributed to a nonexistent KLR rule.

## Actual outline and dependencies

The central question is when a categorical diagonal argument yields an inseparable pair, and how that pair forces incompleteness of theories constructed from syntax and derivations. The comparison theorem uses a range functor together with a lift of a specified partial conditional. The source-conditionals corollary gives inseparability; the theory results then use either a semantic consistency factorization or an inseparable source pair and a total map into sentence codes.

| Existing unit, in compiled reading order | Function and main prerequisites |
|---|---|
| Abstract, PDF p. 1 | State the comparison construction and the arithmetic, Miller, and cosheaf applications. |
| §1 Introduction; §1.1 Related work, PDF pp. 1–3 | Preview the criterion and all applications; give a roadmap; distinguish the incompleteness criterion from existence theorems for recursion categories. |
| §2 Categorical preliminaries, PDF pp. 3–5 | Define the restriction structure, domains, ranges, split completions, products/coproducts, range functors, connectedness, weak choice, and Turing morphisms. |
| §2.1 Partial maps and restriction idempotents | Fix composition, the restriction axioms, totality, orders, compatibility, zeros, inseparability, inverse image, ranges, and splittings. |
| §2.2 Products, coproducts, and local connectedness | Supply the finite categorical structure and explain why range-functor preservation does not include product preservation. |
| §2.3 Recursion categories | Fix the prodominical, isotypical, and parameterized Turing properties used later. |
| §3 Diagonal comparison and complementary conditionals, PDF pp. 5–7 | Prove the comparison theorem, the obstruction for lifted separators, and the source inseparability criterion. |
| §3.1 The comparison theorem | Construct a total diagonal parameter map from a source lift; compare inverse images of two disjoint target domains. Depends on §2's Turing property and coproduct comparison. |
| §3.2 Complementary conditionals | Derive source inseparability from total source conditionals; show disjoint joins supply them. Appendix C explains why lifting cannot simply be removed. |
| §4 Internal theories and semantic consistency, PDF pp. 7–9 | Connect theorem ranges, semantic validity, and incompleteness. Uses Appendix A's syntax and derivation construction explicitly. |
| §4.1 Theories and their interpretation | Define the sentence theorem idempotent; extend a range functor through chosen restriction splittings; prove the interpretation proposition. |
| §4.2 Incompleteness from semantic consistency | State and prove `thm:logical-comparison`, using the comparison theorem plus a total map to sentences and a soundness/disjointness hypothesis. |
| §4.3 Inseparability in the source | Prove `cor:domain-incompleteness`; explain why original-object inseparability survives restriction splitting. |
| §5 The syntactic recursion category, PDF pp. 9–22 | Construct the PA-provable-graph quotient and then its total splitting, syntax, substitution, and theories. |
| §5 opening construction | Distinguish object terms, numerical codings, indices, graph formulas, and equivalence classes. Establish composition, ranges, products, coproducts, and the Turing morphism. Compare the unprimed and primed presentations. |
| §5.1 The total restriction splitting | Give the functional-Σ₁ predicate presentation; prove equivalence, regularity, stable disjoint coproducts, partial inverses for monomorphisms, and the partial-map equivalence. |
| §5.2 Syntax and lists | Construct finite sequence/tree codes and parameterized initial algebras for syntax and lists. |
| §5.3 Free variables and substitution | Realize the Appendix A folds algorithmically; retain the original subtree at quantifiers; identify the complemented admissibility domain. |
| §5.4 Derivations and theories | Construct sentence and derivation objects, prove inference-algebra initiality, and prove `thm:syntactic-generated-theory`. |
| §6 Interpretation and soundness, PDF pp. 22–27 | Interpret the quotient in models; construct conditionals; distinguish the arithmetic interpretation of codes from semantic evaluation of decoded formulas. |
| §6.1 Lifting complementary conditionals | Prove witness-search conditionals and their section interpretation; obtain inseparability in `S_T`. |
| §6.2 The total interpretation functor | Define `G_M` and prove preservation of finite limits, coproducts, and regular images. |
| §6.3 Soundness on standard codes | Prove semantic substitution and soundness for standard finite proofs in an arbitrary structure `K` satisfying the axiom set. |
| §6.4 Ultrapowers of the code interpretation | Prove finite-structure/image preservation for the ultrapower functor; construct the natural comparison; transport the soundness factorization and its disjointness. |
| §7 Essential incompleteness of arithmetic, PDF pp. 27–42 | Apply the criterion internally, uniformly in a c.e. axiom index, and in the numerical realization. |
| §7.1 Comparison in the fixed syntactic category | Define provability/refutability and the diagonal domains; prove numeral representation and the partial proof-search lift; prove internal and interpreted incompleteness and recursive inseparability. |
| §7.2 An indexed family of arithmetic theories (`08a`) | Build one axiom/derivation family over an index object, prove the fiber identification through slice equivalences, and define uniform provability. |
| §7.3 Uniform independent sentences (`08b`) | Construct `q:E→S`; for every consistent fiber, its value is independent of that theory. Depends on the indexed family and the parameterized Turing property. |
| §7.4 The numerical realization (`08c`) | Construct the category of c.e. numerical carriers; prove its regular/partial-map equivalences; realize syntax and proofs; compare code presentations. |
| §7.5 Numerical incompleteness (`08d`) | Construct a fixed recursively inseparable numerical pair; prove domain inclusions into arithmetic theorem/refutation domains; apply the source criterion. |
| §7.6 Numeral instances and theory extension | Define the pair category and the covariant assignment under theory inclusion; compare the argument with Bernardi's precomplete-equivalence-relation method. |
| §8 Miller sequences and essential incompleteness, PDF pp. 42–48 | Turn Miller's indexed real property into an oracle-independent recursion category, inseparable cuts, and essentially incomplete real-closed-field theories. |
| §8.1 Computation independent of the binary representation | Prove the compactness/unanimity lemma and categorical properties; distinguish common domain and values from a computation with a fixed oracle. |
| §8.2 The index sets below and above 1/2 | Give the total recursive cut reduction; prove source inseparability; exhibit separators for each fixed representation and nonpreservation of the chosen Turing morphism. |
| §8.3 A theory of real closed fields | Define `E_a`-semidecidability and the splitting presentation; realize syntax/theory construction; prove essential incompleteness of `T_a`. |
| §9 A recursion category from a three-point space, PDF pp. 48–55 | Construct a different recursion-category example and c.e. propositional theories via component evaluation. |
| §9 opening construction | Define cosheaves, the space, the fork diagram category, partial-map category, universal object, frame, and recursion subcategory. State the completion equivalences with precise appendix references. |
| §9.1 Complementary domains and inseparability | Build complementary conditionals explicitly, apply the criterion, and distinguish the category from numerical recursion by the terminal-subobject invariant. |
| §9.2 Evaluation functors | Define all three evaluations and prove endpoint Turing universality; describe the endpoint probes; exhibit failure of universality at component zero. |
| §9.3 Propositional theories and component theorem sets | Build initial formula/proof algebras, theorem ranges, consistency, compatible c.e. extensions, and the endpoint essential-incompleteness corollary. |
| Appendix A Syntax and deductively closed theories, PDF pp. 55–64 | Supply the general construction invoked earlier. |
| A.1 Categorical hypotheses and notation | State regularity/extensivity assumptions; define Boolean morphisms, conditionals, product-expression convention, decidable variables, and parameter stability. |
| A.2 Terms, formulas, and free variables | Define the two-sorted polynomial functor, initial syntax/list algebras, constructors, folds, free-variable occurrence lists, and sentence pullback. |
| A.3 Admissible substitution | Construct option-valued substitution by an algebra retaining original expressions; identify admissibility and prove identity/absent-variable substitution. |
| A.4 Inference rules and deductively closed subobjects | Define the inference endofunctor and closure; prove that the regular image of an initial derivation algebra is least closed. |
| A.5 First-order theories | Give all seven logical schemes, rule objects and side conditions; construct sentence theories; compare regular images with ranges under explicit partial-inverse hypotheses. |
| A.6 Propositional theories | Specialize to atom, negation, implication, and modus ponens; retain positive/negative atomic axiom images. |
| Appendix B The three-point cosheaf construction, PDF pp. 64–71 | Prove the structural and universality claims used in §9. |
| B.1 Cosheaves and functor categories | Prove the cosheaf–fork equivalence; show why values at the whole space do not compute products/subobjects pointwise; prove regularity and extensivity. |
| B.2 Partial maps, ranges, and connected restriction idempotents | Give component domain/value formulas, range/union/pullback laws, weak choice, and local connectedness. |
| B.3 A universal object and a frame | Construct embeddings and product/coproduct/nonempty-word isomorphisms. |
| B.4 A Turing morphism | Build endpoint and zero-component programs, check their common natural domain, and construct typed parameter maps for arbitrary source objects. |
| B.5 The recursion category and its splitting | Prove the full-subcategory and completion equivalences; give the terminal-subobject and nondecidable-equality distinctions. |
| Appendix C Necessity of section lifting, PDF pp. 71–73 | Give a counterexample with `K`-c.e. domains and ordinary recursive extensions, a Turing morphism, a separated diagonal pair, and a target section lacking a source lift. |
| Appendix D Faithful families and theory extension, PDF pp. 73–76 | Build the faithful all-model interpretation and explain its interaction with extension and numeral observations. |
| D opening construction | Define the model index set and product category; prove faithfulness and target structural properties; give the commuting extension square. |
| D.1 Inseparable pairs under theory extension | Prove persistence of the constructed pair; distinguish the image of a Turing morphism from target universality and source conditionals from arbitrary target separators. |
| D.2 Numeral observations | Define `E_T(c)` and identify proof-enumerated standard instances with categorical equalities using numeral constants. |
| D.3 A complete ambient theory | Identify the true-arithmetic quotient with extensional numerical recursion; show that categorical inseparability alone does not imply incompleteness of the ambient theory. |
| Bibliography, PDF pp. 76–77 | Supply 31 source entries and links. Factual bibliographic verification is delegated to the citation audit. |

No revised global outline is warranted by this prose review. In particular, moving Appendix A wholesale before the applications would postpone the motivating results by nine pages; the existing explicit forward references give the reader a workable path. The long numerical comparison in §7.4 establishes code and proof-object dependencies subsequently used in §§7.5–7.6 and §9. It should not be removed simply to shorten the paper.

## Comparison table: local findings

All file anchors below are relative to `tmp/audit_v29/frozen/local_connectedness/`. Line numbers are source line numbers, not invented PDF line numbers.

| ID / status | Manuscript anchor | Actual difficulty | Principle / rationale | Recommended action |
|---|---|---|---|---|
| O1, optional, highest priority | `sections/01-introduction.tex:3–10`, PDF p. 1 | The first sentence leads with “Corollary 3.3” and takes roughly forty words to reach its conditions. The central aim is only inferable from the title and abstract. The separate sentence about inverse images can initially read as a general fact rather than a hypothesis of the criterion. | KLR §1 points 12, 13, 17, 24. | Replace this paragraph with the text below. Preserve the next paragraph and its counterexample reference. |
| O2, optional | `sections/08-essential-incompleteness-of-arithmetic.tex:244–251`, PDF p. 30 | “Every consistent c.e. extension of it” uses a pronoun where the statement moves between PA and an arbitrary extension of PA. A reader can recover the meaning, but naming the quantified theory makes the essential-incompleteness assertion immediate. | KLR §1 point 17; independent request for explicit quantifiers. | Name `T` in the statement and repeat it in the extension clause, as below. |
| O3, optional | `appendices/b-three-point-cosheaves.tex:599–601,621–628`, PDF p. 71 | Appendix B calls the *first* summand the equality-true summand, whereas Appendix A names the second injection `t` and uses its inverse image for the diagonal. Both conventions are explicitly stated and the local proof is coherent, but the switch gives a reader one avoidable convention to remember. | KLR §1 point 14. This is consistency polish, not a mathematical error. | Use the second summand in the Appendix B definition and its proof; exact text below. |
| O4, optional | `sections/03a-internal-theories.tex:94–103`, PDF p. 8 | `Par(E,Mono)` first appears here, while its span presentation and `Mono` notation are explained explicitly much later in §9 and Appendix A. The notation is familiar to the intended audience, and no omission is alleged; a short parenthetical would reduce a forward lookup. | KLR §1 point 11, qualified by §§4–5. | Add one sentence identifying the monic-span presentation at this first use; do not duplicate its composition proof. |
| C1, resolved by the separate full-text citation audit | `appendices/a-syntax-and-theories.tex:169–175`, PDF p. 57 | “These treatments identify expressions up to renaming of bound variables” grammatically covers FPT, Gabbay–Pitts, and Katsumata. It is a blanket factual attribution to three treatments, not just a description of this manuscript's syntax. | Primary-source attribution must match the actual cited objects and equalities. | The syntax citation worker reports that FPT §§2–4, Gabbay–Pitts §6, and Katsumata §2 Example 1(3) all support the attribution (see `citations_syntax.md` and its JSON ledger). Retain the sentence and the raw-names/admissibility distinction. I have not independently retrieved those texts. |

**Required versus optional.** None of O1–O4 is a mathematical blocker, a missing proof, or evidence that a result is false. I found no separate prose defect requiring a source edit as a condition of understanding the definitions and statements. C1 is supported according to the separate syntax citation audit; this writing review has not independently retrieved those three papers. No wording repair is recommended there.

## Definition order and notation audit

The introduction and abstract are previews. They need not contain full categorical definitions. The body then follows this introduction order:

| Term / notation | First substantive treatment and definition | Finding |
|---|---|---|
| Composition `gf`, total/partial arrow conventions | `02-categorical-preliminaries.tex:5–28`; Appendix A repeats at 24–32 | Explicitly fixed as `g∘f`, with `f` applied first. No order ambiguity found. |
| Restriction category, restriction idempotent/domain, total morphism, `Tot(C)` | `02:5–28` | Defined before proofs use them. Domains as idempotents are distinguished from concrete subsets by the partial-function explanation at 57–60. |
| Restriction functor and restriction equivalence | `02:23–28` | Defined explicitly; no absent definition. Appendix A:677–685 recalls the relevant preservation law at its use. |
| Restriction orders, compatibility, joins, zeros, complementary and inseparable pairs | `02:30–44` | Explicit equations and quantifiers supplied. Source separation and target separation remain distinct throughout the applications. |
| Inverse image `f* a` | `02:46–48` | Defined as a restriction idempotent using the partial arrow `f`; totality is stated separately where needed for preservation of top or completeness. |
| Receiving idempotent and `ran(f)` | `02:49–60` | Leastness and agreement law both stated. Later image comparisons preserve the distinction between categorical ranges and regular images. |
| Restriction splitting and `Split(C)` | `02:62–76` | Objects, morphisms, identities and relative totality all explicit. `e` is the identity of `(X,e)`, preventing confusion with `1_X`. |
| Karoubi envelope | `02:78–85` | Distinguished from restriction splitting by arbitrary versus restriction idempotents; the induced restriction operation is given. Mathematical validation of this operation belongs to the foundations audit. |
| Binary restriction product/coproduct, diagonal/codiagonal | `02:89–113` | Arrow types and universal equations are present. The product pairing's restricted projections are not suppressed. |
| Range functor and `χ_{X,Y}` | `02:115–132` | Preserved structures, comparison type and copairing equation supplied. The product counterexample gives content to the later product-preservation distinction and should be retained. |
| Connected/local connectedness, partial monomorphism, section, weak choice | `02:134–147` | Defined before use. “Jointly epimorphic” is immediately spelled out as the arrow-testing condition. |
| Prodominical, isotypical, Turing morphism, recursion category | `02:151–165` | All defined. The Turing property quantifies over every object `X`, every appropriate partial `f`, and a total parameter map `r`. |
| Source/target domains `a_0,a_1,P,N`; source lift `ℓ`; target conditional `s` | `03:18–45` | Types, defining inverse images, disjointness, reduction inequalities and lift equality all stated. Do not compress this into an untyped phrase such as “the lift exists.” |
| Sentence object and sentence theorem `t_A` | `03a:5–42`, with definitions explicitly delegated to Appendix A:191–196,264–275,585–596 | Locally introduced with object and map types; Appendix A gives the general construction. No missing definition. |
| Restriction monomorphism | `03a:29–32` explains the term at its first use by its partial-inverse equations; Appendix A:613–616 gives a general definition | Adequate first explanation, although the full general definition is later. **Do not report this term as undefined.** |
| `F̂`, `E_e,m_e,r_e`, and `κ_{e,d}` | `03a:44–92` | Choices and object/arrow actions explicit. Domain object, ambient object, and selected splitting are distinguished. |
| `Par(E,Mono)` | First occurrence `03a:104`; explicit span explanation `09:68–80`, Appendix A:653–657 | Familiar standard notation; optional first-use pointer O4. This is late expansion, not absence. |
| Object terms `O`, carriers `|X|`, codings `γ_X`, index sets `I(X,Y)` | `05:3–50` | Formal terms, sets, numeric codes and typed indices distinguished. Equality of object terms is syntactic. |
| `Tr`, `out`, graph predicate `G`, fixed graph `G_e` | `05:34–45` | All indices/trace variables and primitive-recursive abbreviations declared. Numerals versus model-carrier elements are clarified later. |
| Provable index equality `≡_T` and classes `[e]_T` | `05:91–107` | Universal graph equality and composition independence given. No confusion with extensional equality in `Rec`. |
| Primed equality and failure of representative independence | `05:126–138` | Pointwise equality is displayed and distinguished from the unprimed relation. The negative result is mathematical content and should be retained subject to citation verification. |
| Domain representatives `[C]_T`, range representatives `[R_e]_T` | `05:140–180` | Witness-search realization, order equivalence and agreement proof supplied. |
| `B_T`, predicate category `P_T`, functional search | `05a:4–39,41–73` | Objects, represented morphisms, equivalence of representations, supports and totality explicit. Formula and represented morphism shorthand is declared. |
| “Provably surjective” | `05a:151–166` | Locally defined by a universal theorem of `T`; not confused with truth in the standard model. |
| Finite list codes and finite Σ₁ membership | `05a:281–313` | Representation, constructor injectivity and the witness-sequence argument are given. Witnesses are distinct from syntax/derivation codes. |
| Coefficient objects `V,Σ_k,Π_k`, arity `d`, parser/tree-size convention | `05a:315–370` | Carriers and bounded arities explicit; numerical equality on variables justified. |
| Parameter stability and `K_P` | Formal general definition Appendix A:148–157; §5a:372–390 explicitly references that sense | Acceptable forward definition with local sources/targets made explicit. Do not invent a missing-initiality objection from the order alone. |
| `FV`, term substitution, option-valued formula substitution, `Adm` | §5a:513–618; general definitions Appendix A:225–245,247–275,280–404 | Raw named variables, failure values, admissibility and successful results distinguished. In particular, the `y=x` branch uses the original body even if recursive body substitution failed. |
| `Sent`, `P_A`, conclusion index, generated theorem predicate | `05a:624–635,637–806,808–878` | All constructed. The difference between the full conclusion object and sentence pullback is maintained. |
| Model interpretation `F_M`, code bijection `γ_X^M`, total interpretation `G_M` | `06:6–29,125–139` | Explicit domains and codomains. Quantified computation traces range over the whole model, including nonstandard elements. |
| Arithmetic code model `N` versus semantic structure `K` | `06:167–210` | The manuscript explicitly distinguishes interpretation of code objects from satisfaction of decoded formulas. Preserve this explanation. |
| `U(X)=X^I/∼_U`, ultrapower comparison `η` | `06:346–357,400–451` | Equivalence relation, functor action, comparison components and naturality equation are explicit. Representative choices are subsequently shown independent. |
| `Prov_Γ`, `Th_Γ`, `Ref_Γ`, `α,β,D_0,D_1,Θ,Neg,θ` | `08:15–113` | Defined in stages, with sentence carriers and totality explicitly tracked. `M≡N` is stated where transfer of true arithmetic sentences is used; no silent replacement by arbitrary `M⊨PA`. |
| Index family `E,Γ_e,Ax(e,z)`, family proof object and `Prov(e,z)` | `08a:4–132,139–333` | Each local category, parameter object, rule, slice, comparison and standard index is given. The fiber argument retains its categorical dependencies. |
| Uniform independent-sentence map `q:E→S` | `08b:4–84` | The consistency quantifier applies separately to each numerical fiber. The construction does not assume a uniform decision of consistency. |
| `Rec` and `C_rec`; carrier/function shorthand `|C|,|f|,f(x)` | `08c:4–36` | Extensional partial functions are separated from provable graph classes. An object is a dimension/carrier pair, not merely a subset without an ambient dimension. |
| `Q,F,Q̃,Q_num`, tuple coding `κ_m` | `08c:38–320` | Object and arrow actions, spans, domains and natural comparison components are explicitly typed. These details support §9 and should not be replaced by a blanket assertion of equivalence. |
| Numerical pair `A,B`, numerical theorem domains and inclusions | `08d:10–81` | Link to the previously fixed `α,β,Θ` supplied. The original-object inclusion is full; inseparability in its splitting is justified. |
| `Pair(Rec)` and numeral observations `P_T,N_T` | `08:290–314` | Objects, arrows, containment conditions, identities and composition defined. No absent definition of the pair category. |
| Cantor space, `Q,ρ,P_z`, computing a real, Miller property | `04:3–42` | Topologies, binary representations, rational approximation and the strengthened indexed property are explicitly given. The representation can change approximants while preserving the computed real. |
| `τ_z`, `E_a`, fixed-oracle `Rec^p`, `J_p,I_p` | `04:47–183` | Universal oracle quantifier and common-domain requirement explicit; fixed-oracle interpretation distinguished from oracle-independent computation. |
| `L_a,R_a`, recursive reduction `h`, separators `C_p` | `04:188–302` | Strict inequalities and the `a(n)=1/2` case explained. This is a substantive endpoint distinction, not a disclaimer. |
| `E_a`-semidecidability, `D_a`, `T_a` | `04:307–440` | Explicit definitions precede the real-closed-field theorem. The theorem uses the given language and a semidecidable axiom set, rather than an unstated arbitrary presentation. |
| Cosheaf, space `X`, fork category `J`, c.e. subfunctor | `09:10–66` | All defined. Set-valued cosheaves and effective numerical diagrams are related by an explicitly named underlying-set functor. |
| Universal object `V`, nonempty words `Y#`, frame, `R_X` | `09:84–149`; Appendix B:248–342 | Types and standard source reference for “frame” given. “Universal object” is explained by its embedding/partial-inverse property. |
| Evaluations `E_j`, endpoint probes `H_i,Φ_i`, `|e|_i` | `09:197–282` | Object/arrow actions and natural isomorphism supplied. Endpoints `i=1,2` are not silently conflated with component zero. |
| Formula/proof functors `P,H`, theorem subfunctor, compatible family | `09:360–586` | Constructor and rule types, slice equations, relabelings, closure and consistency all explicit. |
| Regular category/image, kernel pair, extensive coproducts | Appendix A:13–22 and Appendix B:63–77 | Standard notions are recalled where the abstract construction needs them. The repetition is useful for appendix use, not an empty reassurance. |
| Boolean operations, variables as projections, quantifier order | Appendix A:24–157 | Morphisms are constructed on named sources and the shorthand convention is declared. The truth operations are verified as morphism identities after jointly epimorphic injections. |
| Closure/inference algebra and sentence theory | Appendix A:419–596 | The theory is a subobject satisfying a stated closure/factorization condition, not an untyped collection of proofs. |
| `K`, `W_a^K`, `C_K`, recursive extension `f_0` | Appendix C:8–45 | Ordinary recursive computation, `K`-c.e. domain, and the resulting partial graph are expressly distinguished. This distinction is essential to the counterexample. |
| All-model family `M_T,D_T,F_T`, quotient functor and projection | Appendix D:3–91 | Underlying carrier `N` is distinguished from standard arithmetic; numeral interpretation is not identified with the carrier element. Functor types and composition laws explicit. |
| Numeral observation `E_T(c)`, constant maps `κ_n`, true arithmetic quotient | Appendix D:147–184 | Standard natural-number observations and equality of syntactic morphisms are connected by explicit equivalences. Completeness of the ambient theory is not inferred from categorical inseparability. |

**Confirmed omissions:** no missing major definition was found in the complete source. The only first-use expansion recommendation is O4, which concerns familiar partial-map notation explained later. This conclusion does not cover mathematical validity or factual literature claims.

## Exact replacement text for the optional edits

### O1: introductory paragraph

Replace `sections/01-introduction.tex:3–10` only with:

```latex
We prove a categorical inseparability criterion and apply it to
essential incompleteness of formal theories. The comparison theorem
uses a range functor and a lift of a specified partial morphism into
a binary coproduct. When total inverse images in the target preserve
binary joins of restriction idempotents, total source morphisms that
select opposite coproduct summands on complementary domains yield
an inseparable diagonal pair
(Corollary~\ref{cor:source-conditionals}). The range functor need
not preserve restriction products.
```

This remains a preview; the nonzero-object condition and the remaining categorical hypotheses must remain in the full theorem and corollary. Retain the following paragraph about disjoint joins and Appendix C. It explains a necessary restriction through a concrete counterexample.

### O2: name the theory in the corollary

Replace the statement text at `sections/08-essential-incompleteness-of-arithmetic.tex:247–251`, preserving both labels and the environment, with:

```latex
For every consistent c.e.\ extension $T$ of PA, the theorem and
refutation sets of sentence codes of $T$ are recursively inseparable.
Each such $T$ is essentially incomplete: every consistent c.e.\
extension of $T$ is incomplete.
```

### O3: keep the truth-summand convention consistent

Replace `appendices/b-three-point-cosheaves.tex:599–601` with:

```latex
\emph{Decidable equality} on $V$ means a morphism
$\epsilon:V\times V\to1+1$ in $\mathcal E$ whose inverse image of
the second summand is the diagonal subfunctor, as in
Appendix~\ref{app:categorical-hypotheses}.
Here $1$ is the terminal object of $\mathcal E$.
```

In the proof at lines 625–626 change only “lies in the first summand” to “lies in the second summand.” The later “same summand” then refers to that summand. The proof's mathematical distinction between a full diagonal and its chosen Boolean name is preserved.

### O4: identify partial-map notation at first occurrence

After “for a regular category `$\mathcal E$`” in `sections/03a-internal-theories.tex:103–105`, add this sentence after the sentence containing that hypothesis, without placing it inside the hypothesis:

```latex
Here $\Mono$ denotes all monomorphisms of $\mathcal E$, and
$\Par(\mathcal E,\Mono)$ is the category of spans with monic left
leg, composed by pullback.
```

An alternative placement that avoids breaking the proposition is immediately before its statement. Prefer that placement if the author wants the proposition to remain short. This is the sole optional repair for which placement, rather than mathematical wording, is left to the author.

## Economy, paragraph purpose, and material to retain

The complete source contains no prompt, agent instruction, chat reference, proof-audit checklist, “this revision fixes” passage, or other editorial-process narration in its compiled text or source comments. The README is not an input to `main.tex`; its drafting-status prose is outside the manuscript and is not treated as a manuscript defect. The bibliography's title *Corrections to More existence theorems for recursion categories* is a bibliographic title and must not be edited as alleged process prose.

The following passages should be retained despite repeated or negative wording:

| Anchor | Mathematical function that would be lost by deletion |
|---|---|
| `02:123–132` | Concrete counterexample showing that a range functor need not preserve restriction products. |
| `05:126–138` | Distinction between pointwise provability and uniform graph equality, with the resulting representative-independence obstruction. |
| `05a:442–444` | Identifies the induction principles actually available in `T`; the algebra operations are only total on their carrier predicates. This is a proof premise, not a retrospective reassurance. |
| `05a:564–579,608–618`; Appendix A:314–331,406–414 | Explains the quantifier reset branch and the transfer of absent-variable conditions. These are needed for capture avoidance and the substitution identities. |
| `05a:732–735` | Marks the fact that an arbitrary inference-algebra program is total on its specified source, rather than every numerical input. The subsequent fold proof uses that distinction. |
| `06:24–29,188–199` | Separates nonstandard computation traces and arithmetic code interpretation from satisfaction of decoded formulas in `K`. |
| `08:263–271` | States why a partial source proof-search lift is sufficient: totality in `S_PA` is not an assumption of the comparison theorem. |
| `04:39–42,282–302` | Separates representation-dependent rational approximations and fixed-oracle separators from common-domain, common-value source morphisms. |
| `09:284–295` | Gives a concrete failure of zero-component Turing universality; the endpoint qualification cannot be deleted. |
| Appendix B:44–61 | Concrete product and monomorphism examples show why categorical subobjects are not pointwise subsets at every open set of the cosheaf. |
| Appendix C:21–29,165–197 | Separates source domains from ordinary recursive extensions and proves that a target conditional lacks a source lift. |
| Appendix D:125–142,174–184 | Shows that target universality and arbitrary target separators differ from their source counterparts, and that an inseparable source pair alone does not imply ambient-theory incompleteness. |

The adjectives “ordinary,” “standard,” “partial,” “strict,” “faithful,” and “consistent” generally identify mathematical distinctions here. In particular, “standard codes” contrasts with nonstandard model elements, and “ordinary recursive” contrasts with an oracle computation. They should not be removed by a blanket adjective pass. The few occurrences of “structural” modify actual encodings or structural recursion; none was found serving only as praise. “Genuine” and “actual” do not occur as manuscript padding. No new terminology or diagram is recommended: the existing typed TikZ squares already serve the multi-path arguments, and the short compositional identities are readable as equations.

## Scope and file coverage

The reviewed source root is `/workspace/scratch/9e446291e628/tmp/audit_v29/frozen/local_connectedness`. Files read in full:

| File | Lines read |
|---|---:|
| `main.tex` | 1–25 |
| `preamble.tex` | 1–43 |
| `abstract.tex` | 1–16 |
| `sections/01-introduction.tex` | 1–137 |
| `sections/02-categorical-preliminaries.tex` | 1–166 |
| `sections/03-sections-and-inseparability.tex` | 1–167 |
| `sections/03a-internal-theories.tex` | 1–256 |
| `sections/05-syntactic-recursion-category.tex` | 1–203 |
| `sections/05a-internal-syntax.tex` | 1–878 |
| `sections/06-interpretation-in-models.tex` | 1–536 |
| `sections/08-essential-incompleteness-of-arithmetic.tex` | 1–331, with nested inputs read at their compiled positions |
| `sections/08a-uniform-theories.tex` | 1–333 |
| `sections/08b-uniform-independent-sentences.tex` | 1–86 |
| `sections/08c-numerical-realization.tex` | 1–595 |
| `sections/08d-numerical-incompleteness.tex` | 1–81 |
| `sections/04-miller-sequences.tex` | 1–498 |
| `sections/09-three-point-space.tex` | 1–645 |
| `appendices/a-syntax-and-theories.tex` | 1–711 |
| `appendices/b-three-point-cosheaves.tex` | 1–629 |
| `appendices/c-section-lifting.tex` | 1–198 |
| `appendices/d-faithful-family.tex` | 1–184 |
| `bibliography.tex` | 1–144, all 31 entries |

The supplied v29 PDF has 77 pages. I extracted its complete text for heading/page localization and visually inspected its first page; this is **not** a claim of complete visual layout QA. I did not compile, edit, or mathematically certify the manuscript. Full-text verification of its other cited sources and bibliographic claims belongs to the separate citation audit. No old version, old diff, or standalone companion note was substituted for this source pass.

The paragraph-purpose inventory follows. Its anchors refer to blank-line source paragraph groups, including theorem/proof groups when the source does not insert a blank line between them. Headings and `\input` directives are listed separately or omitted as nonparagraph material. Each group has a mathematical function; no group was identified whose sole role was an empty assurance that an unstated mistake had been avoided.


## Paragraph-purpose inventory


### `abstract.tex`

| Source lines | Function | Opening anchor |
|---|---|---|
| 1–15 | State the central results and applications | `We derive essential incompleteness from a categorical construction of inseparable pairs. The co` |

### `sections/01-introduction.tex`

| Source lines | Function | Opening anchor |
|---|---|---|
| 3–10 | State the inseparability criterion | `Corollary~\ref{cor:source-conditionals} establishes inseparability of restriction idempotents i` |
| 12–16 | Explain a sufficient hypothesis and counterexample | `Joins of source morphisms with disjoint domains supply complementary conditionals (Proposition~` |
| 18–33 | Preview the Miller construction and separator distinction | `The principal application uses a sequence $a:\N\to[0,1]$ constructed by Miller \cite{Miller2004` |
| 35–43 | Preview the real-closed-field application | `This example gives a theory of real closed fields with constants $c_n$ and the strict rational ` |
| 45–62 | Preview the syntactic category and model interpretation | `We also apply the criterion to the syntactic recursion categories of Montagna and Di Paola--Mon` |
| 64–78 | Preview numerical and cosheaf applications | `The numerical instance of the criterion gives a fixed recursively inseparable pair. Finite comp` |
| 80–93 | Give the dependency roadmap | `After the preliminaries, Section~\ref{sec:lifting} proves the comparison theorem and the criter` |
| 97–105 | Compare or attribute the mathematical construction | `Di Paola and Heller proposed inseparability of theorems and refutable sentences as part of a ca` |
| 107–116 | Compare or attribute the mathematical construction | `Di Paola and Heller introduced dominical categories as a setting for recursion theory \cite{DPH` |
| 118–126 | Compare or attribute the mathematical construction | `Di Paola and Heller proved recursive inseparability in dominical recursion categories in which ` |
| 129–137 | Compare or attribute the mathematical construction | `Miller constructed a sequence that enumerates every real in $[0,1]$ computable uniformly from i` |

### `sections/02-categorical-preliminaries.tex`

| Source lines | Function | Opening anchor |
|---|---|---|
| 5–28 | Compare or attribute the mathematical construction | `Composition is written $gf=g\circ f$, so $f$ is applied first. A \emph{restriction category} is` |
| 30–44 | Explain a construction, implication or application | `Restriction idempotents on $X$ are ordered by $a\le b$ when $ba=a$. Their meet is composition, ` |
| 46–60 | Compare or attribute the mathematical construction | `For $f:X\rightharpoonup Y$ and a restriction idempotent $a$ on $Y$, the \emph{inverse image} of` |
| 62–76 | Compare or attribute the mathematical construction | `A restriction idempotent $e$ on $X$ \emph{splits} if $e=mr$ for a total $m:A\to X$ and $r:X\rig` |
| 78–85 | Compare or attribute the mathematical construction | `The \emph{Karoubi envelope} $\operatorname{Kar}(\mathcal C)$ has the same description with arbi` |
| 89–104 | Compare or attribute the mathematical construction | `A \emph{binary restriction product} $X\times Y$ has total projections $\pi_1:X\times Y\to X$ an` |
| 106–113 | Explain a construction, implication or application | `Binary \emph{restriction coproducts} are categorical coproducts with total injections $i_0:X\to` |
| 115–132 | Explain a construction, implication or application | `A \emph{range functor} $F:\mathcal C\to\mathcal D$ preserves restrictions, ranges, restriction ` |
| 134–147 | Explain a construction, implication or application | `A restriction idempotent $a$ on $X$ is \emph{connected} if, for restriction idempotents $b,c$ o` |
| 151–154 | Explain a construction, implication or application | `A restriction category with binary restriction products and zeros is \emph{prodominical} if $f\` |
| 156–165 | Compare or attribute the mathematical construction | `A \emph{Turing morphism} on $U$ is a morphism $\tau:U\times U\rightharpoonup U$ such that, for ` |

### `sections/03-sections-and-inseparability.tex`

| Source lines | Function | Opening anchor |
|---|---|---|
| 3–8 | Explain the diagonal construction | `The diagonal argument compares a pair of source restriction idempotents with two disjoint targe` |
| 10–14 | Define objects, maps or conventions for the construction | `For a coproduct $Y+Z$, let $\varepsilon_0=1_Y+0_Z$ and $\varepsilon_1=0_Y+1_Z$ be its summand r` |
| 18–53 | State the result and begin its proof | `Let $\mathscr R$ be a recursion category with ranges and binary restriction coproducts, let $\m` |
| 55–79 | Prove the preceding result / construction | `Write $E=Fg:FU\to FU$ and $H=\chi_{U,U}^{-1}Fh:FU\rightharpoonup FU+FU$. Applying $F$ to the pr` |
| 81–98 | State the result and begin its proof | `Under the hypotheses of Theorem~\ref{thm:comparison} on $\mathscr R$, $\mathcal A$, $F$, $\tau$` |
| 102–129 | State the result and begin its proof | `Under the hypotheses of Theorem~\ref{thm:comparison} on $\mathscr R$, $\mathcal A$, $F$, $\tau$` |
| 131–145 | Prove the preceding result / construction | `If $c,c'$ separated $a_0,a_1$, put $P=F(c)$ and $N=F(c')$. These are complementary target restr` |
| 147–164 | State the result and begin its proof | `Let $\mathcal C$ be a restriction category with restriction zeros and binary restriction coprod` |
| 166–167 | Point to the lifting counterexample | `Appendix~\ref{app:lifting-counterexample} gives a faithful range functor and a complementary ta` |

### `sections/03a-internal-theories.tex`

| Source lines | Function | Opening anchor |
|---|---|---|
| 5–42 | Define objects, maps or conventions for the construction | `Let $\mathscr R$ be a restriction category with ranges, restriction zeros, and binary restricti` |
| 44–63 | Define objects, maps or conventions for the construction | `Let $F:\mathscr R\to\mathcal A$ be a range functor, where $\mathcal A$ is a split restriction c` |
| 65–75 | Explain a construction, implication or application | `This extension preserves ranges. To see this, write $a=\ran(f)\le d$, where the same restrictio` |
| 77–92 | Explain a construction, implication or application | `The coproduct of $(X,e)$ and $(Y,d)$ in $\mathscr S$ is $(X+Y,e+d)$. The canonical morphism \[ ` |
| 94–134 | State the result and begin its proof | `Let $F:\mathscr R\to\mathcal A$ be a range functor with split target, let $\widehat F:\Split(\m` |
| 136–140 | Explain the soundness application | `For an interpretation of the syntax with a validity subobject $v:V\hookrightarrow\widehat F S$,` |
| 144–190 | State the result and begin its proof | `Let $\mathscr R,\mathcal A,F,U,\tau,b,a_0,a_1$ satisfy the categorical hypotheses and definitio` |
| 192–205 | Prove the preceding result / construction | `If $t\vee(\widehat F\nu)^*t=1_{\widehat F S}$, inverse image along the total morphism $\widehat` |
| 209–210 | Motivate the source-pair criterion | `An inseparable pair in the source category gives an alternative criterion that applies to every` |
| 212–240 | State the result and begin its proof | `Let $\mathcal C$ be a restriction category with restriction zeros and binary joins of restricti` |
| 242–248 | Explain preservation by restriction splitting | `An inseparable pair on an object of $\mathscr R$ remains inseparable in $\Split(\mathscr R)$: t` |
| 250–256 | Identify applications and dependencies | `Section~\ref{sec:arithmetic} applies Theorem~\ref{thm:logical-comparison} to a soundness factor` |

### `sections/05-syntactic-recursion-category.tex`

| Source lines | Function | Opening anchor |
|---|---|---|
| 3–32 | Define objects, maps or conventions for the construction | `Let $T$ be a consistent extension of $\PA$ in the language of arithmetic. Fix in the metatheory` |
| 34–50 | Compare or attribute the mathematical construction | `Use the deterministic computation coding for Kleene's trace predicate as in \cite[p.~115, Note~` |
| 52–89 | State the result and begin its proof | `For this computation coding, there are an index $u\in\N$ and primitive-recursive functions $\op` |
| 91–100 | Explain a construction, implication or application | `The objects of $S_T$ are the terms in $\mathsf O$. Its morphisms $X\rightharpoonup Y$ are the e` |
| 102–107 | Define objects, maps or conventions for the construction | `For $e\in\mathcal I(X,Y)$ and $f\in\mathcal I(Y,Z)$, define $[f]_T[e]_T=[\operatorname{comp}(f,` |
| 109–124 | Compare the set and formal-term presentations | `Montagna's objects are the sets generated from $\N$ by Cartesian products and the displayed dis` |
| 126–138 | Distinguish pointwise equality and composition failure | `The pointwise relation used in the primed systems identifies $e,f\in\mathcal I(X,Y)$ when, for ` |
| 140–180 | Compare or attribute the mathematical construction | `For $X\in\mathsf O$ and a $\Sigma_1$ arithmetic formula $C(x)$, where $x$ is the numerical code` |
| 182–202 | Explain a construction, implication or application | `The pairing and tagged-coproduct constructions on indices have PA-provable graph equations: pai` |

### `sections/05a-internal-syntax.tex`

| Source lines | Function | Opening anchor |
|---|---|---|
| 4–12 | Introduce the total splitting and predicate presentation | `The syntax and theory construction of Appendix~\ref{app:syntax-theories} will be applied in \[ ` |
| 14–39 | Define objects, maps or conventions for the construction | `Let $\mathcal P_T$ have as objects the $\Sigma_1$ arithmetic formulas $C(x)$ with the displayed` |
| 41–63 | State the result and begin its proof | `For every $\Sigma_1$ formula $\Gamma(x,y)$ there is an index $a_\Gamma$ such that PA proves \fo` |
| 65–73 | Prove the preceding result / construction | `PA proves by induction on the number of tests that a halting run returns the first successful t` |
| 75–103 | State the result and begin its proof | `There is an equivalence \[ \mathcal P_T\simeq\mathcal B_T. \] The category $\mathcal B_T$ is re` |
| 105–117 | Prove the preceding result / construction | `Conversely, a total morphism from $(\omega,[C]_T)$ to $(\omega,[D]_T)$ has a graph satisfying \` |
| 119–149 | Prove the preceding result / construction | `We prove the remaining claims in $\mathcal P_T$. The predicate $x=0$ is terminal: the unique mo` |
| 151–166 | Prove the preceding result / construction | `Call a represented morphism $\varepsilon:C\to D$ \emph{provably surjective} when \[ T\vdash\for` |
| 168–178 | Prove the preceding result / construction | `Such a split epimorphism is the coequalizer of its kernel pair. Indeed, let $k_0,k_1:K\rightrig` |
| 180–192 | Prove the preceding result / construction | `Every $\Gamma:C\to D$ factors through $R_\Gamma$ by the same graph, followed by the identity in` |
| 194–224 | Prove the preceding result / construction | `The false predicate is initial. If $C$ admits a morphism to it, totality gives $T\vdash\forall ` |
| 226–256 | Prove the preceding result / construction | `It remains to analyze arbitrary monomorphisms. Let $\Gamma:C\to D$ be monic and form its kernel` |
| 258–268 | Construct the partial-map equivalence | `In particular, there is a restriction equivalence \[ \Par(\mathcal B_T,\Mono)\simeq\Split(S_T).` |
| 270–276 | Explain the extension of ranges | `Ranges extend to $\Split(S_T)$ by the same representatives. For a morphism $f:(X,e)\rightharpoo` |
| 281–290 | Define objects, maps or conventions for the construction | `We use primitive-recursive codes for finite sequences with length, entry, and concatenation ope` |
| 292–313 | State the result and begin its proof | `Let $C(x)$ be $\Sigma_1$. The assertion that all entries of a coded finite sequence satisfy $C$` |
| 315–326 | Define objects, maps or conventions for the construction | `Fix a nonnegative integer $d$ and objects \[ V,\quad \Sigma_0,\ldots,\Sigma_d,\quad \Pi_0,\ldot` |
| 328–338 | Define objects, maps or conventions for the construction | `We choose codes for raw, finite, ordered syntax trees as follows. A code is a canonical sequenc` |
| 340–344 | Explain a construction, implication or application | `Each constructor concatenates its ordered child blocks and appends its root record. Its decompo` |
| 346–370 | Explain a construction, implication or application | `The formula $\operatorname{Tm}(t)$ asserts that this parser accepts $t$ as a term, that variabl` |
| 372–392 | State the result and begin its proof | `Let $d$ be a nonnegative integer and let $V,\Sigma_k,\Pi_k$ be objects of $\mathcal B_T$ for $0` |
| 394–406 | Prove the preceding result / construction | `Fix an arbitrary object $P$ and an arbitrary $K_P$-algebra with carriers $\xi:X\to P$ and $\ups` |
| 408–417 | Prove the preceding result / construction | `Define relations $\operatorname{Ev}_{\mathrm{Tm}}(p,t,x)$ and $\operatorname{Ev}_{\mathrm{Fm}}(` |
| 419–424 | Prove the preceding result / construction | `All these requirements are $\Sigma_1$. Boundedly many carrier and projection requirements are c` |
| 426–440 | Prove the preceding result / construction | `The following is an induction proof in $T$. Induct simultaneously for terms and formulas on the` |
| 442–444 | Prove the preceding result / construction | `This argument uses the finitely many totality and projection equations of the given algebra as ` |
| 446–458 | Prove the preceding result / construction | `Lemma~\ref{lem:syntactic-functional-search} now supplies indices for the two evaluation relatio` |
| 460–471 | Prove the preceding result / construction | `Let $(h'_{\mathrm{Tm}},h'_{\mathrm{Fm}})$ be any other such algebra morphism. Its totality and ` |
| 473–489 | State the result and begin its proof | `For every object $V$ of $\mathcal B_T$, the endofunctor $Z\mapsto1+V\times Z$ has an initial al` |
| 491–504 | Prove the preceding result / construction | `For an algebra in $\mathcal B_T/P$ on an arbitrary projection $\xi:X\to P$, its nil operation i` |
| 509–511 | Connect initiality to the substitution algorithms | `The preceding propositions supply the initiality hypotheses of Definition~\ref{def:categorical-` |
| 513–537 | State the result and begin its proof | `On the preceding codes, the list operations, free-variable maps, term substitution, and the opt` |
| 539–550 | Prove the preceding result / construction | `A postfix traversal computes the free-variable list. At a variable it returns the singleton lis` |
| 552–562 | Prove the preceding result / construction | `For substitution, use a traversal which retains at each node both its original subtree and its ` |
| 564–579 | Prove the preceding result / construction | `At a quantified formula $\forall y\,\varphi$, let $z$ be the computed option value for its body` |
| 581–590 | Prove the preceding result / construction | `The traversal is primitive recursive: it runs through the finite postfix sequence, storing fini` |
| 592–606 | Prove the preceding result / construction | `Success and failure are decidable tags of this total option-valued algorithm on its source. The` |
| 608–618 | Prove the preceding result / construction | `Finally, simultaneous induction in $\mathrm{PA}$ proves identity substitution and substitution ` |
| 624–635 | Define objects, maps or conventions for the construction | `Let $\operatorname{fv}_{\Fm}(z)$ denote the numerical free-variable list function just construc` |
| 637–653 | State the result and begin its proof | `Let $T\supseteq\PA$, let $F$ be an object of $\mathcal B_T$, and fix morphisms \[ p_n:R_n\longr` |
| 655–675 | Prove the preceding result / construction | `First fix codes for finite ordered trees in which a node of arity $n\leq N$ has a numerical lab` |
| 677–693 | Prove the preceding result / construction | `Define $P(d)$ to assert that $d$ is such a tree and that, at every node with label $r$, arity $` |
| 695–713 | Prove the preceding result / construction | `For a tree $d$ whose root has arity $n$ and label $r$, put \[ C(d,z)\ \equiv\ P(d)\land G_{v_n}` |
| 715–730 | Prove the preceding result / construction | `The constructor equations for the node list give, in $T$, &P\bigl(\operatorname{node}_n(r,d_1,\` |
| 732–735 | Prove the preceding result / construction | `Let $\alpha:H(Q,q)\to(Q,q)$ be any algebra in this slice. Represent $Q$ by $Q(y)$, $q$ by an in` |
| 737–765 | Prove the preceding result / construction | `Define $E_a(d,y)$ to assert that $d$ is a tree and there is a finite list of values, one for ea` |
| 767–796 | Prove the preceding result / construction | `Induction on the numerical tree code now proves in $T$ that each $d$ satisfying $P(d)$ has an e` |
| 798–806 | Prove the preceding result / construction | `If $g:(P,c)\to(Q,q)$ is another algebra morphism, its algebra-morphism equation gives the same ` |
| 808–821 | State the result | `Let $T$ be a consistent extension of $\PA$ and put $\mathcal B_T=\Tot(\Split(S_T))$. Fix a nonn` |
| 823–845 | Prove the preceding result / construction | `Use the displayed sentence predicate, and choose the derivation predicate $P_A(p)$ and conclusi` |
| 847–854 | Prove the preceding result / construction | `Every rule object in Appendix~\ref{app:first-order-derivations} is a finite product, coproduct,` |
| 856–870 | Prove the preceding result / construction | `The original morphism $[e_A]_T:\omega\rightharpoonup\omega$ has restriction $[P_A]_T$ and range` |
| 872–878 | Apply the generated-theory result to arithmetic | `For the arithmetic signature, a $\Sigma_1$ predicate $\operatorname{Ax}_T(z)$ enumerating the a` |

### `sections/06-interpretation-in-models.tex`

| Source lines | Function | Opening anchor |
|---|---|---|
| 3–4 | Identify the concrete target structure | `In $\Pfn$, restriction products are Cartesian products and coproducts are tagged disjoint union` |
| 6–29 | Define objects, maps or conventions for the construction | `Fix a model $M\models T$. Assign a set $X_M$ to each term $X\in\mathsf O$ by \[ X_M=\|M\|\quad(X=` |
| 31–44 | State the result and begin its proof | `For every $M\models T$, \eqref{eq:model-functor} defines a covariant functor $F_M:S_T\to\Pfn$ p` |
| 46–56 | Prove the preceding result / construction | `The definedness predicate $\exists y\,G_e(x,y)$ gives the interpreted function's domain. Simila` |
| 60–89 | State the result and begin its proof | `Let $c,c'$ be complementary restriction idempotents on $X$ in $S_T$. There is a total morphism ` |
| 91–101 | Prove the preceding result / construction | `Interpret this proved graph identity in $M\models T$. Under the canonical coproduct identificat` |
| 103–120 | State the result and begin its proof | `For every $M\models T$, the functor $F_M$ satisfies the hypotheses of Corollary~\ref{cor:source` |
| 125–139 | Define the total interpretation functor | `For a model $M\models T$, split each interpreted restriction idempotent in $\Pfn$ by its domain` |
| 141–163 | State the result and begin its proof | `For every $M\models T$, the functor $G_M$ preserves finite limits, finite coproducts, and regul` |
| 167–186 | Fix standard-code syntax and the axiom subobject | `Fix the arithmetic signature and the variable object $V=(\omega,1_\omega)\in\mathcal B_{\PA}$, ` |
| 188–199 | Distinguish code interpretation from semantic validity | `For $s\in G_{\N}S$, let $\varphi_s$ be the finite sentence with code $s$. Let $K\models\Gamma$ ` |
| 201–210 | Type the interpreted admissibility inclusion | `Let $j_{\Adm}:\Adm\hookrightarrow\Fm\times V\times\Tm$ be the admissibility inclusion in $\math` |
| 212–245 | State the result and begin its proof | `Let $\sigma:\N\to \|K\|$ be an assignment of values to variables. For $x\in\N$ and $a\in\|K\|$, wri` |
| 247–253 | Prove the preceding result / construction | `Induction on $r$ proves the term identity. At a variable it is the two-case definition of subst` |
| 255–275 | Prove the preceding result / construction | `Consider $\varphi=\forall y\,\psi$ and put $a=\llbracket t\rrbracket^K_\sigma$. If $y=x$, subst` |
| 277–301 | State the result and begin its proof | `Let $\Gamma$ be a computably enumerable set of arithmetic sentences, with axiom subobject $i_A:` |
| 303–318 | Prove the preceding result / construction | `For universal instantiation, if $\forall x\,\varphi$ holds at $\sigma$, then $\varphi$ holds at` |
| 320–325 | Prove the preceding result / construction | `Every nonlogical axiom is a sentence satisfied by $K$, and hence is valid under every assignmen` |
| 327–336 | Prove the preceding result / construction | `By Lemma~\ref{lem:syntactic-derivation-initiality}, each element of $G_{\N}P_A$ is the code of ` |
| 338–342 | Prove the preceding result / construction | `By Proposition~\ref{prop:st-substitution-realization} and the constructor realization, $G_{\N}\` |
| 346–357 | Define the ultrapower functor | `Work in the usual set-theoretic metatheory with choice. Fix a nonempty set $I$ and a proper ult` |
| 359–376 | State the result and begin its proof | `The functor $\mathscr U:\mathbf{Set}\to\mathbf{Set}$ preserves finite limits, finite coproducts` |
| 378–394 | Prove the preceding result / construction | `For a family in $X\amalg Y$, exactly one of the sets of indices carrying the two tags belongs t` |
| 396–398 | Apply Łoś’s theorem | `Let $M=\N^I/\mathcal U$ be the arithmetic ultrapower. \L o\'s's theorem~\cite[Theorem~3.1]{Keis` |
| 400–422 | State the result and begin its proof | `There is a natural isomorphism of functors \[ \eta:\mathscr U G_{\N}\xRightarrow{\ \cong\ }G_M:` |
| 424–429 | Prove the preceding result / construction | `For a morphism represented by a functional graph $\Gamma:C\to D$, let $d_i$ be its value at $c_` |
| 431–451 | Prove the preceding result / construction | `To define the comparison on $\mathcal B_{\PA}$, for each object $B$ choose an isomorphism $u_B:` |
| 453–504 | State the result and begin its proof | `Let $i_A:A\hookrightarrow S$ and $K$ satisfy the hypotheses of Proposition~\ref{prop:standard-c` |
| 506–513 | Prove the preceding result / construction | `The factorization places the regular image of $G_Mc_{A,S}$ inside $v_{K,\mathcal U}$. Propositi` |
| 515–528 | Explain validity membership in representatives | `For $s\in G_MS$, choose a family $(s_i)_{i\in I}$ in $G_{\N}S$ such that $s=\eta_S([s_i])$. The` |
| 530–536 | Explain evaluation on proof representatives | `Likewise, for $p\in G_MP_{A,S}$, choose a family $(p_i)_{i\in I}$ in $G_{\N}P_{A,S}$ such that ` |

### `sections/08-essential-incompleteness-of-arithmetic.tex`

| Source lines | Function | Opening anchor |
|---|---|---|
| 6–13 | Fix the sentence objects and negation | `Fix the arithmetic signature and its realization in $\mathcal B_{\PA}=\Tot(\Split(S_{\PA}))$ fr` |
| 15–39 | Define the axiom and provability data | `Let $\Gamma$ be a computably enumerable set of arithmetic sentences. Choose a $\Sigma_1$ formul` |
| 41–54 | Identify theorem and refutation sets | `Under the standard interpretation, the set $G_{\N}P_\Gamma$ consists of the codes of finite der` |
| 56–86 | Define diagonal domains and numeral substitution | `Use the Turing morphism $\tau_{\PA}=[u]_{\PA}:\omega\times\omega\rightharpoonup\omega$ and the ` |
| 88–113 | State the result and begin its proof | `There is a total morphism $\theta:\omega\to S$ in $\mathcal B_{\PA}$ such that \[ (G_{\N}\theta` |
| 115–141 | Prove the preceding result / construction | `PA-provable functionality of $G$ and disjointness of even and odd numbers give \[ \PA\vdash\for` |
| 143–182 | State the result and begin its proof | `For every c.e.\ sentence set $\Gamma$, there is a morphism $\ell_\Gamma:\omega\rightharpoonup\o` |
| 184–190 | Prove the preceding result / construction | `In a model where $C,C'$ are disjoint, $R$ is functional. If $M\models R(x,z)$, the second displ` |
| 192–216 | State the result and begin its proof | `Let $\Gamma$ be a consistent c.e.\ set of arithmetic sentences from which every PA-axiom is der` |
| 218–242 | Prove the preceding result / construction | `Apply Theorem~\ref{thm:logical-comparison} with $\mathscr R=S_{\PA}$, $\mathcal A=\Pfn$ and $F=` |
| 244–271 | State the result and begin its proof | `For every consistent c.e.\ extension of PA, its theorem and refutation sets of sentence codes a` |
| 273–280 | Prove the preceding result / construction | `The same argument applies to every consistent c.e.\ extension. If such a theory were complete, ` |
| 290–314 | Define the observation pairs and covariant assignment | `Use the numerical objects of Section~\ref{subsec:numerical-incompleteness}. For a consistent c.` |
| 320–331 | Compare with precomplete equivalence relations | `Bernardi's numerical argument uses a precomplete equivalence relation $R$ on $\N$: for every pa` |

### `sections/08a-uniform-theories.tex`

| Source lines | Function | Opening anchor |
|---|---|---|
| 4–17 | Explain a construction, implication or application | `We construct one derivation object for all computably enumerable axiom sets containing the chos` |
| 19–33 | Define objects, maps or conventions for the construction | `Choose a $\Sigma_1$ formula $\operatorname{Ax}_{\PA}(z)$ for the codes of the chosen sentence a` |
| 35–63 | Define objects, maps or conventions for the construction | `We specify the numerical presentation of the axiom family. Let $J=J_{\PA}:\mathcal P_{\PA}\to\m` |
| 65–124 | Define objects, maps or conventions for the construction | `Let $L,R_1,R_2\in\mathcal B$ and \[ \lambda:L\to\Fm,\qquad p_n:R_n\to\Fm^n,\qquad q_n:R_n\to\Fm` |
| 126–131 | Define objects, maps or conventions for the construction | `For $e\in\N$, let $\epsilon_e:1\to E$ be the numeral morphism. For $X\in\mathcal B$, let $!_X:X` |
| 133–191 | State the result and begin its proof | `For every $e\in\N$, the pullback of $c^{\mathrm{all}}$ along $k_e^{\Fm}$ is the underlying conc` |
| 193–250 | Prove the preceding result / construction | `Write $F_{\ne e}=E_{\ne e}\times\Fm$, and let $\pi_E:F_E\to E$ be the product projection. For $` |
| 252–276 | Prove the preceding result / construction | `The equivalence $\Xi_e$ and the natural isomorphism $\zeta$ induce an equivalence \[ \Lambda_e:` |
| 278–295 | Prove the preceding result / construction | `Let $(\mathfrak P_e,\mathfrak P_{\ne e})=\Lambda_e(\mathfrak P)$. This pair is initial in $\ope` |
| 297–302 | Prove the preceding result / construction | `Pulling back the conclusion morphisms along $j:S\hookrightarrow\Fm$ gives the displayed square.` |
| 304–333 | Define objects, maps or conventions for the construction | `Choose a $\Sigma_1$ predicate $P_0(d)$ and a presentation isomorphism $u:J(P_0)\xrightarrow{\co` |

### `sections/08b-uniform-independent-sentences.tex`

| Source lines | Function | Opening anchor |
|---|---|---|
| 4–44 | State the result and begin its proof | `For the family $\Gamma_e$ and objects $E,S\in\mathcal B=\Tot(\Split(S_{\PA}))$ of Section~\ref{` |
| 46–65 | Prove the preceding result / construction | `Recall the Turing morphism $\tau_{\PA}:\omega\times\omega\rightharpoonup\omega$, the isomorphis` |
| 67–86 | Prove the preceding result / construction | `Fix $e\in\N$ with $\Gamma_e$ consistent, and put $n=F_{\N}(g)(e)\in\N$. Choose a first-order st` |

### `sections/08c-numerical-realization.tex`

| Source lines | Function | Opening anchor |
|---|---|---|
| 4–16 | Define objects, maps or conventions for the construction | `For $X,Y\in\mathsf O$ and $e\in\mathcal I(X,Y)$, define the partial function $\varphi_e:\|X\|\rig` |
| 18–28 | Define objects, maps or conventions for the construction | `Write $\mathcal C=\mathcal C_{\mathrm{rec}}$, $\mathscr S_{\mathrm{rec}}=\Split(\mathrm{Rec})$,` |
| 30–35 | Define objects, maps or conventions for the construction | `For each $m\geq0$, choose an injective recursive tuple coding $\kappa_m:\N^m\to\N$ with recursi` |
| 38–68 | State the result and begin its proof | `There is an equivalence \[ \operatorname{Tot}(\operatorname{Split}(\mathrm{Rec})) \simeq\mathca` |
| 70–103 | Prove the preceding result / construction | `For $(X,e)\in\mathcal B_{\mathrm{rec}}$, let $D_e=\gamma_X(\operatorname{dom}e)\subseteq\N$, an` |
| 105–112 | Prove the preceding result / construction | `The singleton $(0,\{()\})$ is terminal in $\mathcal C$. Products are Cartesian products of carr` |
| 114–130 | Prove the preceding result / construction | `The object $(1,\varnothing)$ is initial. For $C=(m,C_0)$ and $D=(n,D_0)$, choose their coproduc` |
| 132–154 | Prove the preceding result / construction | `For $f:C\to D$ in $\mathcal C$, define the image object $\operatorname{Im}(f)$ to have the dime` |
| 156–171 | Prove the preceding result / construction | `Computable singleton maps distinguish any two elements of a carrier. Consequently a monomorphis` |
| 173–190 | Prove the preceding result / construction | `Define a functor \[ \widetilde Q:\operatorname{Par}(\mathcal C,\operatorname{Mono}) \longrighta` |
| 192–238 | Prove the preceding result / construction | `Define a quasi-inverse \[ \mathsf Q_{\mathrm{num}}:\mathscr S_{\mathrm{rec}} \longrightarrow\ma` |
| 240–279 | Prove the preceding result / construction | `Regard each $u_C:FQ(C)\to C$ as a total isomorphism in $\mathcal K_{\mathrm{rec}}$. For a parti` |
| 281–305 | State the result and begin its proof | `Fix $d\ge0$, let $V=(1,\N)$, and let $\Sigma_k=(1,\Sigma_{k,0})$ and $\Pi_k=(1,\Pi_{k,0})$ have` |
| 307–330 | Prove the preceding result / construction | `Fix $P\in\mathcal C_{\mathrm{rec}}$. In $(\mathcal C_{\mathrm{rec}}/P)^2$, put \[ \mathbf T_P=(` |
| 332–359 | Prove the preceding result / construction | `On input $(p,t)\in\|P\|\times\|\Tm\|$ or $(p,\varphi)\in\|P\|\times\|\Fm\|$, parse the tree and evaluat` |
| 361–392 | Prove the preceding result / construction | `Let $W\in\mathcal C_{\mathrm{rec}}$ be the object of dimension one whose carrier is the recursi` |
| 394–422 | Prove the preceding result / construction | `The free-variable and substitution algorithms in Propositions~\ref{prop:st-list-initiality} and` |
| 424–451 | Prove the preceding result / construction | `Fix an axiom subobject $i_A:A\hookrightarrow S$ in $\mathcal C_{\mathrm{rec}}$. Retain $A$ itse` |
| 453–474 | Prove the preceding result / construction | `For any object $(Q,q)$ of $\mathcal C_{\mathrm{rec}}/\Fm$ and algebra $\beta:H_A(Q,q)\to(Q,q)$ ` |
| 476–496 | Define objects, maps or conventions for the construction | `For arithmetic, choose exactly the signature labels and numerical syntax codes used in Section~` |
| 498–569 | Explain a construction, implication or application | `To compare with the syntactic category, write $S^{\mathrm{syn}}\in\mathcal B_{\PA}$ and $c_T^{\` |
| 571–595 | Define objects, maps or conventions for the construction | `Put $\mathscr S_{\mathrm{rec}}=\Split(\mathrm{Rec})$ and transport these objects and total maps` |

### `sections/08d-numerical-incompleteness.tex`

| Source lines | Function | Opening anchor |
|---|---|---|
| 5–10 | Define objects, maps or conventions for the construction | `Use the numerical realization and comparison functors of Section~\ref{subsec:numerical-realizat` |
| 12–27 | Explain a construction, implication or application | `The denotation $\tau_{\mathrm{rec}}=\varphi_u:\omega\times\omega\rightharpoonup\omega$ is a Tur` |
| 29–54 | Explain a construction, implication or application | `The functor $J_{\mathrm{rec}}:\mathrm{Rec}\to\Pfn$ has $J_{\mathrm{rec}}(X)=\|X\|$ and $J_{\mathr` |
| 56–81 | Define objects, maps or conventions for the construction | `For a c.e.\ arithmetic presentation $T$ containing the PA sentence axioms, use $S_{\mathrm{rec}` |

### `sections/04-miller-sequences.tex`

| Source lines | Function | Opening anchor |
|---|---|---|
| 3–27 | Define representations and oracle computation of reals | `Let $2^{\N}=\{0,1\}^{\N}$ be the set of infinite binary sequences, with the product topology of` |
| 29–42 | Compare or attribute the mathematical construction | `Miller's construction gives a sequence $a\in Q$ with the following property: if an oracle progr` |
| 47–73 | State the result and begin its proof | `There is one oracle program which, from $p\in P_z$ and numerical inputs $e,n$, computes the par` |
| 75–87 | Prove the preceding result / construction | `For fixed $e,n,m$, let \[ H_{e,n,m}=\{q\in2^{\N}:\Phi_e^q(n)\mathord\downarrow=m\}. \] Finite h` |
| 89–95 | Define objects, maps or conventions for the construction | `For the fixed sequence $a$, let $\mathcal E_a$ have the objects generated from $\N$ by binary C` |
| 97–118 | State the result and begin its proof | `The category $\mathcal E_a$ is a locally connected recursion category with ranges, binary restr` |
| 120–127 | Prove the preceding result / construction | `For every input $x$, the singleton partial identity $1_{\{x\}}$ is recursive. It is connected, ` |
| 129–142 | Prove the preceding result / construction | `Lemma~\ref{lem:miller-unanimity} puts $\tau_a$ in $\mathcal E_a$. Let $f:X\times\N\rightharpoon` |
| 144–160 | Define objects, maps or conventions for the construction | `For $p\in P_a$, let $\mathrm{Rec}^{p}$ be the recursion category on the same numerical objects,` |
| 162–183 | Explain a construction, implication or application | `If $c,c':X\rightharpoonup X$ are complementary restriction idempotents in $\mathcal E_a$, run t` |
| 188–195 | Define the two strict cut sets | `Define \[ L_a=\{n:a(n)<\tfrac12\},\qquad R_a=\{n:a(n)>\tfrac12\}. \] Their partial identities b` |
| 197–220 | State the result and begin its proof | `There is an ordinary total recursive map $h:\N\to\N$ such that \[ h^{-1}(L_a)=A_0,\qquad h^{-1}` |
| 222–254 | Prove the preceding result / construction | `The product topology on $Q$ is induced by the metric \[ d:Q\times Q\to[0,1],\qquad d(z,w)=\sum_` |
| 256–272 | Prove the preceding result / construction | `The preceding construction gives one oracle program computing total numerical functions $\Psi^p` |
| 274–293 | State the result and begin its proof | `The restriction idempotents $1_{L_a},1_{R_a}:\N\rightharpoonup\N$ are inseparable in $\mathcal ` |
| 295–301 | Explain a construction, implication or application | `If $J_p\tau_a$ were a Turing morphism, Corollary~\ref{cor:source-conditionals}, applied to $I_p` |
| 307–315 | Define semidecidability and the concrete splitting | `Call a subset $D$ of a numerical object \emph{$\mathcal E_a$-semidecidable} when its partial id` |
| 317–319 | Define objects, maps or conventions for the construction | `Put $\mathcal D_a=\operatorname{Tot}(\operatorname{Split}(\mathcal E_a))$. The following realiz` |
| 321–346 | State the result and begin its proof | `The category $\mathcal D_a$ is regular, with finite coproducts that are disjoint and stable und` |
| 348–358 | Prove the preceding result / construction | `For $f:C\to D$, dovetail its computations over all numerical inputs to semidecide its image. A ` |
| 360–370 | Prove the preceding result / construction | `Singleton maps detect noninjectivity, so the monomorphisms are exactly the injections. For an i` |
| 372–388 | Prove the preceding result / construction | `Numerical equality makes $V=\N$ decidable. Encode terms and formulas as finite labeled ordered ` |
| 390–399 | Prove the preceding result / construction | `The free-variable and substitution folds of the appendix consequently exist in $\mathcal D_a$. ` |
| 401–412 | Prove the preceding result / construction | `Represent an axiom subobject by its semidecidable image in the sentence carrier. Use the seven ` |
| 414–424 | Prove the preceding result / construction | `For any $H_A$-algebra, first semidecide that the input is a valid derivation, then evaluate it ` |
| 426–440 | Define the field axioms and exhibit a model | `Consider the language of ordered fields with additional constants $(c_n)_{n\in\N}$. Its symbol ` |
| 442–478 | State the result and begin its proof | `Let $a$ be a Miller sequence with property~\eqref{eq:miller-property}, and let $T_a$ be the the` |
| 480–498 | Prove the preceding result / construction | `For $n\in L_a$, the sentence $c_n<1/2$ is an axiom of $T_a$. For $n\in R_a$, the axiom $1/2<c_n` |

### `sections/09-three-point-space.tex`

| Source lines | Function | Opening anchor |
|---|---|---|
| 3–8 | Preview the construction and incompleteness result | `We construct a recursion category $\mathscr R_X$ from cosheaves on a three-point space $X$. For` |
| 10–24 | Define cosheaves and the Sierpiński space | `For a topological space $X$, let $\mathcal O(X)$ be the category of open sets and inclusions. A` |
| 26–39 | Define the three-point space and fork presentation | `Let $X=\{a,b,c\}$ have opens $\varnothing,\{c\},\{a,c\},\{b,c\},X$. The open subspaces $\{a,c\}` |
| 41–48 | Recall the carrier convention | `Use the category $\mathcal C_{\mathrm{rec}}$ of Section~\ref{subsec:numerical-realization}. Its` |
| 50–66 | Define effective fork diagrams and subfunctors | `Put $\mathcal E=\mathcal C_{\mathrm{rec}}^J$. An object is a covariant functor $Y:J\to\mathcal ` |
| 68–82 | Define partial maps by monic spans | `In the notation $\operatorname{Par}(\mathcal C,\operatorname{Mono})$, $\operatorname{Mono}$ den` |
| 84–125 | Define the universal object, words, frame and subcategory | `Define an object $V:J\to\mathcal C_{\mathrm{rec}}$ of $\mathcal E$ by the following objects $V_` |
| 127–134 | Apply the Turing construction | `Theorem~\ref{thm:fork-turing} constructs a Turing morphism $\tau:V\times V\rightharpoonup V$ in` |
| 136–149 | Explain completion equivalences and syntax placement | `Every object $Y$ of $\mathcal E$ admits a total map $m:Y\to V$ in $\mathcal A$ with a partial i` |
| 153–193 | Construct conditionals and prove categorical distinction | `Proposition~\ref{prop:fork-local} proves that $\mathcal A$ is locally connected. Its splitness,` |
| 197–214 | Define the component evaluation functors | `Let $\mathcal K=\operatorname{Par}(\mathcal C_{\mathrm{rec}},\operatorname{Mono})$. Its objects` |
| 216–231 | State the result and begin its proof | `The covariant functors $E_j$ preserve restrictions, zeros, ranges, binary restriction products ` |
| 233–252 | Prove the preceding result / construction | `Use the recursive bijection $\operatorname{encode}_2:\N^2\to\N$, its inverse $\operatorname{dec` |
| 254–282 | Construct probes and the natural comparison | `For $i\in\{1,2\}$, let $H_i:J\to\mathcal C_{\mathrm{rec}}$ have component $\{*\}$ at $i$ and em` |
| 284–295 | Exhibit failure of zero-component universality | `The functor $E_0$ does not preserve this Turing morphism's universality. The total function $F:` |
| 299–333 | Construct the inseparable component pair | `Let $\zeta:V\to V+V$ be the coproduct isomorphism of Lemma~\ref{lem:fork-frames}. At each compo` |
| 335–352 | Apply the source criterion at the endpoints | `The restriction $U\|_{\mathcal K_2}:\mathcal K_2\to\Pfn$ preserves restrictions, zeros, and rang` |
| 354–358 | Introduce the propositional realization | `The category $\mathcal E$ is regular with finite coproducts, and its images are componentwise i` |
| 360–381 | Construct formula trees and the formula functor | `For $j=0,1,2$, let $S_j$ be the set of finite rooted ordered formula trees with constructors \[` |
| 383–394 | State the result and begin its proof | `The algebra $\iota$ is initial: for every $\alpha:P(Z)\to Z$ in $\mathcal E$, there is a unique` |
| 396–403 | Prove the preceding result / construction | `Write $z_i=Z(0\to i):Z_0\to Z_i$. Naturality of $\alpha$ says that $z_i$ commutes with each con` |
| 405–436 | Define the logical and atomic axiom maps | `The logical axiom schemes define morphisms $\Lambda_1,\Lambda_3:S^2\to S$ and $\Lambda_2:S^3\to` |
| 438–467 | Construct the inference endofunctor | `Write $\pi_1,\pi_2:S^2\to S$ for the projections and put $\mu=\langle\pi_1,\Rightarrow\rangle:S` |
| 469–479 | Construct the c.e. derivation carriers | `At component $j$, a derivation is a finite rooted ordered tree. Each leaf is labeled by a membe` |
| 481–490 | Construct proof relabelings | `For $i=1,2$, relabel formula parameters by $\sigma_i$ and atomic axiom labels by $r_i^V$, retai` |
| 492–500 | Construct the proof-algebra operations | `Forming a leaf and adjoining a modus-ponens root give morphisms $\ell:\mathrm{Ax}\to\mathrm{Prf` |
| 502–518 | State the result and begin its proof | `The algebra $\delta$ is initial. For every $\eta:\mathsf H(Q,q)\to(Q,q)$ in $\mathcal E/S$, the` |
| 520–527 | Prove the preceding result / construction | `Naturality of $\eta$, $\lambda$, and the pullback projections makes each evaluation step commut` |
| 529–531 | Define the theorem range | `For a restriction idempotent $t$ on $S$, let $D_t\subseteq S$ be the c.e. subfunctor on which $` |
| 533–556 | State the result and begin its proof | `The subfunctor $D_{t_0}\subseteq S$ is the least c.e. subfunctor containing the logical and pos` |
| 558–571 | Prove the preceding result / construction | `For consistency, fix $j$ and suppose derivations $p,q$ conclude $\varphi$ and $\nu_j\varphi$. L` |
| 573–586 | Define compatible theory extensions and completeness | `Write $\sigma_i=S(0\to i):S_0\to S_i$ for $i=1,2$. A compatible family of c.e.\ theory extensio` |
| 588–613 | State the result and begin its proof | `Fix $i\in\{1,2\}$. Let $T\subseteq S$ be a compatible family of consistent c.e.\ theory extensi` |
| 615–625 | Prove the preceding result / construction | `The atom map $E_i\theta:\N^2\to S_i$ is total recursive. The component theorem and refutation s` |
| 627–630 | Prove the preceding result / construction | `If $T\subseteq T'$, monotonicity gives inclusions of both component sets, so the identity of $\` |
| 632–645 | State the result and begin its proof | `For each $i\in\{1,2\}$, the propositional theory with theorem set $(D_{t_0})_i$ is essentially ` |

### `appendices/a-syntax-and-theories.tex`

| Source lines | Function | Opening anchor |
|---|---|---|
| 5–8 | Explain the general construction | `We define first-order syntax by categorical structure and construct the theory generated by an ` |
| 13–22 | State categorical hypotheses | `Let $\mathcal D$ be a regular category with finite coproducts. Thus $\mathcal D$ has finite lim` |
| 24–32 | Fix composition, parentheses and powers | `Composition is $gf=g\circ f$. Finite products and coproducts are chosen and parenthesized to th` |
| 34–79 | Construct Boolean morphisms | `Put $\Two=1+1$, with injections $\mathbf{f},\mathbf{t}:1\to\Two$. Pulling this coproduct back a` |
| 81–104 | Prove Boolean algebra identities as morphism identities | `These morphisms make $\Two$ a Boolean algebra object in $\mathcal D$. Indeed, distributivity ex` |
| 106–122 | Construct conditionals | `Let $p:X\to\Two$. Write $[p=\mathbf{t}]\hookrightarrow X$ for its pullback along $\mathbf{t}$; ` |
| 124–128 | Define the product-expression convention | `We use variables to abbreviate projections from a displayed product. An expression built from t` |
| 130–146 | Fix decidable variables and coefficient objects | `Fix an object $V\in\operatorname{Ob}(\mathcal D)$ and a morphism $\epsilon:V\times V\to\Two$ in` |
| 148–157 | Define parameter stability | `For an endofunctor on the $r$-fold product category $\mathcal D^r$ defined using finite product` |
| 162–167 | Attribute initial-algebra syntax | `Initial many-sorted algebras are used to specify abstract syntax by Goguen, Thatcher, Wagner, a` |
| 169–175 | Compare binding conventions in the literature | `Initial-algebra accounts of binding and substitution are developed by Fiore, Plotkin, and Turi~` |
| 177–189 | Define the two-sorted syntax endofunctor | `Define $K:\mathcal D^2\to\mathcal D^2$ by $K(X,Y)=\bigl(K_1(X,Y),K_2(X,Y)\bigr)$, where K_1(X,Y` |
| 191–196 | Define the named object or closure property | `A raw named-variable syntax object is an initial $K$-algebra $\iota:K(\Tm,\Fm)\to(\Tm,\Fm)$ sta` |
| 198–223 | Type the constructors and explain induction | `The syntax constructors are the following morphisms in $\mathcal D$: \eta:V\to\Tm,\qquad f_k:\S` |
| 225–245 | Construct list operations and their equations | `List initiality with parameters gives concatenation $+\!+:W^2\to W$, membership $\mem:V\times W` |
| 247–262 | Construct free-variable occurrence lists | `Give $(W,W)$ the $K$-algebra defined by singleton lists at variables, ordered concatenation at ` |
| 264–275 | Define the named object or closure property | `The sentence object $s:S\hookrightarrow\Fm$ is the pullback \[ S\arrow[r,hook,"s"]\arrow[d] & \` |
| 280–290 | Define option-valued substitution operations | `We construct substitution of one term for one variable, as required by the logical schemes belo` |
| 292–312 | Construct the algebra retaining original expressions | `In $(\mathcal D/E)^2$, use the carriers \[ X_T=E\times(\Tm\times\Tm)\longrightarrow E, \qquad X` |
| 314–331 | Define the quantified-constructor branch | `For quantification, the operation has source $E\times V\times\Fm\times O(\Fm)$. Denote its proj` |
| 333–358 | State the result and begin its proof | `Parameterized initiality determines morphisms \[ a_T:\Tm\times E\longrightarrow\Tm, \qquad b_F:` |
| 360–379 | Identify the quantified admissibility subobject | `Put $B=V\times\Fm\times E$ and define \[ q=\langle\forall\pi_{V\times\Fm},\pi_E\rangle:B\to\Fm\` |
| 381–404 | State identity and absent-variable substitution | `We write $\varphi[x:=t]$ only on $\Adm$, and $u[x:=t]$ for $a_T(u,x,t)$. Define \[ e_T=\langle\` |
| 406–414 | Prove the substitution identities | `These term and formula statements follow simultaneously by parameterized induction. Atomic step` |
| 419–450 | Attribute finite proof closure and construct the inference functor | `Aczel~\cite[Propositions 1.1.4 and 1.4.5]{Aczel} describes finitary inductive closure by the co` |
| 452–459 | Define the named object or closure property | `A subobject $m:T\hookrightarrow F$ is closed under these rules if there is a morphism $\alpha:\` |
| 461–464 | Explain uniqueness and closure of subobjects | `The algebra structure is unique because $m$ is monic. Its nullary part includes all axioms, and` |
| 466–469 | Explain the factorization argument and attribute the method | `The following proof transfers the initial derivation algebra to its regular image. This is an i` |
| 471–482 | State the result and begin its proof | `With the rule data above, suppose $\delta:H(P,c)\to(P,c)$ is an initial algebra in $\mathcal D/` |
| 484–501 | Prove the preceding result / construction | `Writing $\|H(P,c)\|$ for the underlying object of the slice object, the equations $c\delta=\kappa` |
| 506–552 | Specify logical schemes and their side conditions | `Continue with the syntax structure of Definition~\ref{def:categorical-syntax} and its construct` |
| 554–565 | Define rule objects and their maps | `Fix an axiom subobject $i_A:A\hookrightarrow S$. Define rule objects and their premise and conc` |
| 567–583 | State the result and begin its proof | `Suppose $H_A$ has an initial algebra with conclusion morphism $c_A:P_A\to F$. Its image $T_A\ho` |
| 585–596 | Define sentence theories and prove leastness/monotonicity | `Suppose these initial derivation algebras exist for every axiom subobject of $S$. A \emph{sente` |
| 598–603 | Recall restriction splitting | `For a restriction category $\mathcal R$, its restriction splitting $\Split(\mathcal R)$ has obj` |
| 605–616 | Recall ranges and define restriction monomorphisms | `In a restriction category $\mathcal S$, restriction idempotents $a,b:Y\rightharpoonup Y$ are or` |
| 618–645 | State the result and begin its proof | `Let $\mathcal S$ be a restriction category with ranges in which every restriction idempotent sp` |
| 647–651 | Attribute the relation between ranges and factorizations | `The relation between split ranges and factorizations through restriction monomorphisms is devel` |
| 653–675 | Represent sentence theories as partial identities | `The partial-map category $\Par(\mathcal D,\Mono)$ has morphisms given by spans with monic left ` |
| 677–685 | Explain functoriality of range splittings | `A functor $G:\mathcal S\to\mathcal S'$ between restriction categories with ranges is a \emph{re` |
| 690–711 | Specialize the construction to propositional theories | `Let $\mathcal D$ be regular with finite coproducts, fix an atom object $V\in\operatorname{Ob}(\` |

### `appendices/b-three-point-cosheaves.tex`

| Source lines | Function | Opening anchor |
|---|---|---|
| 5–7 | Fix open-set names and cosheaf morphisms | `Write $D=\{c\}$, $L=\{a,c\}$, and $R=\{b,c\}$ for the nonempty proper opens of $X$. Morphisms o` |
| 9–33 | State the result and begin its proof | `Restriction to $D,L,R$ defines an equivalence $\operatorname{CoSh}(X,\mathbf{Set})\simeq\mathbf` |
| 35–42 | Describe the pushout quotient and its effective relation | `For an object $Y$ of $\mathcal E$, the pushout has a quotient presentation on the tagged carrie` |
| 44–61 | Give product and subobject counterexamples at the whole space | `Products and subobjects are taken in $\mathcal E$. In particular, the cosheaf associated with $` |
| 63–77 | Recall regularity, kernel pairs, slices and extensivity | `A \emph{regular epimorphism} is a coequalizer of a pair of morphisms. A category is \emph{regul` |
| 79–89 | State the result and begin its proof | `The categories $\mathcal C_{\mathrm{rec}}$ and $\mathcal E=\mathcal C_{\mathrm{rec}}^J$ have fi` |
| 91–107 | Prove the preceding result / construction | `Limits and tagged finite coproducts in $\mathcal E$ are formed componentwise. Their universal m` |
| 109–122 | Prove the preceding result / construction | `The three objects of $\mathcal E$ \[ H_0=(1\leftarrow1\to1),\qquad H_1=(1\leftarrow0\to0),\qqua` |
| 124–129 | Prove the preceding result / construction | `Finally, for a map $Y\to A+B$, the inverse images of the two tags form c.e.\ subfunctors $Y^A,Y` |
| 133–162 | State the result and begin its proof | `The category $\mathcal A=\operatorname{Par}(\mathcal E, \operatorname{Mono})$ is a split prodom` |
| 164–176 | Prove the preceding result / construction | `The restriction $\bar f$ is the partial identity on $D_f$. The restriction axioms reduce compon` |
| 178–187 | Prove the preceding result / construction | `The component images $f_j((D_f)_j)$ form a c.e.\ subfunctor $I_f\subseteq Z$. Its partial ident` |
| 189–204 | Prove the preceding result / construction | `For a total $u:W\to Z$, the projection $D_f\times_Z W\to W$ has component image $u_j^{-1}(f_j((` |
| 206–218 | Prove the preceding result / construction | `Suppose that $p:Y\rightharpoonup Z$ is a partial monomorphism and let $D_p$ be its domain subfu` |
| 220–234 | State the result and begin its proof | `The category $\mathcal A$ is locally connected. Let $Y$ be an object of $\mathcal E$. For $y\in` |
| 236–244 | Prove the preceding result / construction | `Suppose that partial morphisms $f,g:Y\rightharpoonup Z$ agree after composition with every conn` |
| 248–253 | Recall the universal object and restriction embeddings | `Let $V$ be the object of $\mathcal A$ defined in \eqref{eq:universal-fork}. A \emph{restriction` |
| 255–272 | State the result and begin its proof | `Every object $Y$ of $\mathcal E$ admits a restriction monomorphism $m:Y\to V$ in $\mathcal A$. ` |
| 274–300 | Construct nonempty words and their semigroup property | `Use the sequence encodings fixed in Section~\ref{sec:cosheaves}. For $Y\in\mathcal E$, define $` |
| 302–306 | Fix encodings for the frame | `Fix a recursive pairing bijection $\pi:\N^2\to\N$ and recursive tuple bijections $\gamma_n:\N^n` |
| 308–317 | State the result and begin its proof | `There are isomorphisms in $\mathcal E$ $V\cong V\times V$, $V\cong V+V$, and $V\cong V^\#$. For` |
| 319–323 | Prove the preceding result / construction | `For the coproduct isomorphism, write $k=2q+t$ with $t\in\{0,1\}$. Send a tuple with first coord` |
| 325–342 | Prove the preceding result / construction | `For the word isomorphism, decode $k$ as the nonempty word $(k_1,\ldots,k_n)$. Decode $z,a,b$ by` |
| 346–348 | Explain the Turing-morphism construction | `We construct a Turing morphism $\tau:V\times V\rightharpoonup V$ in $\mathcal A$ by giving a mo` |
| 350–365 | Fix typed numerical specializations | `Fix recursive bijections $\operatorname{encode}_n:\N^n\to\N$, with recursive inverses $\operato` |
| 367–384 | State the result | `The object $V$ of $\mathcal A=\operatorname{Par}(\mathcal C_{\mathrm{rec}}^J, \operatorname{Mon` |
| 386–392 | Prove the preceding result / construction | `For $i=1,2$, let $T_i\subseteq V_i\times V_i$ be the c.e.\ set on which the numerical computati` |
| 394–420 | Prove the preceding result / construction | `At component $0$, write the parameter and input as \[ P=(k,p_0,p_1,p_2)\in V_0, \qquad x=(\ell,` |
| 422–436 | Prove the preceding result / construction | `If $(P,x)\in T_0$, then \[ (r_i^V P,r_i^V x)=((k,p_i),(\ell,x_i))\in T_i. \] Thus $T=(T_0,T_1,T` |
| 438–460 | Prove the preceding result / construction | `Now let $F:Y\times V\rightharpoonup V$ be any partial morphism. Choose its representation by a ` |
| 462–474 | Prove the preceding result / construction | `Define the component maps of $c:Y\to V$ by c_i(y_i)&=(0,s_i(y_i)) &&(i=1,2),\\ c_0(y)&=(0,s_0(y` |
| 476–502 | Prove the preceding result / construction | `At component $i\in\{1,2\}$, equations \eqref{eq:fork-turing-endpoint} and \eqref{eq:fork-specia` |
| 506–524 | State the result and begin its proof | `Let $\mathscr R_X$ be the full subcategory of $\mathcal A$ whose objects are obtained from $V$ ` |
| 526–531 | Prove the preceding result / construction | `Restrictions and ranges of morphisms between objects of $\mathscr R_X$ are endomorphisms of obj` |
| 533–551 | Prove the preceding result / construction | `For a restriction idempotent $e$ on an object $Y$ of $\mathscr R_X$, write $m_e:D_e\to Y$ and $` |
| 553–567 | State the result and begin its proof | `Every idempotent in $\mathcal A$ splits, and the inclusion $\mathscr R_X\hookrightarrow\mathcal` |
| 569–585 | Prove the preceding result / construction | `For each idempotent $e:Y\rightharpoonup Y$ in $\mathscr R_X$, write $I_e$ for its image subfunc` |
| 587–597 | Recall the numerical completion equivalence | `Use the restriction equivalence \[ \mathsf Q_{\mathrm{num}}:\Split(\mathrm{Rec}) \longrightarro` |
| 599–601 | Fix the decidable-equality convention | `\emph{Decidable equality} on $V$ means a morphism $\epsilon:V\times V\to1+1$ in $\mathcal E$ wh` |
| 603–619 | State the result and begin its proof | `The recursion category $\mathscr R_X$ is not equivalent, as a restriction category, to the recu` |
| 621–628 | Prove the preceding result / construction | `Suppose that $\epsilon$ decides equality on $V$. The functor $1+1$ is constant and sends both n` |

### `appendices/c-section-lifting.tex`

| Source lines | Function | Opening anchor |
|---|---|---|
| 4–6 | State the purpose of the lifting counterexample | `The lifting hypothesis in Theorem~\ref{thm:comparison} cannot be omitted, even for a faithful r` |
| 8–19 | Fix the halting set, oracle domains and coding | `Fix an acceptable numbering $(\varphi_e)_{e\in\N}$ of the ordinary partial recursive functions ` |
| 21–29 | Define the source category and distinguish its morphisms | `The objects of $\mathcal C_K$ are the numerical carriers generated from $\N$ by binary Cartesia` |
| 31–32 | Define the concrete interpretation functor | `Let $F:\mathcal C_K\to\Pfn$ send each numerical carrier to the same set and each morphism to th` |
| 34–45 | Give a numerical presentation of the morphisms | `On $\N$, the morphisms are precisely the functions \[ f_{e,a}(x)\simeq \varphi_e(x),&x\in W_a^K` |
| 47–64 | State the result | `The category $\mathcal C_K$ is a prodominical recursion category with binary restriction coprod` |
| 66–78 | Prove the preceding result / construction | `Let $f:X\rightharpoonup Y$ and $g:Y\rightharpoonup Z$ have ordinary partial recursive extension` |
| 80–86 | Prove the preceding result / construction | `Cartesian products and tagged copairings preserve the morphism class: their domains are respect` |
| 88–97 | Prove the preceding result / construction | `The set $f(D_f)$ is c.e.\ relative to $K$: enumerate $D_f$ and run $f_0$ on its elements. The p` |
| 99–126 | Prove the preceding result / construction | `Define $\tau_K:\N\times\N\rightharpoonup\N$ by \[ \tau_K(\langle e,a\rangle,x)\simeq f_{e,a}(x)` |
| 128–131 | Prove the preceding result / construction | `The functor $F$ is faithful and preserves restrictions, zeros, ranges, binary restriction produ` |
| 133–163 | Prove the preceding result / construction | `Use the total recursive isomorphism \[ b:\N\longrightarrow\N+\N,\qquad b(2n)=i_0(n),\quad b(2n+` |
| 165–189 | Prove the preceding result / construction | `The set $A$ is not recursive. Fix any index $a_*$. Choose an ordinary total recursive function ` |
| 191–197 | Prove the preceding result / construction | `Finally, the morphisms $i_1 1_A$ and $i_0 1_{A^c}$ belong to $\mathcal C_K$: they have the tota` |

### `appendices/d-faithful-family.tex`

| Source lines | Function | Opening anchor |
|---|---|---|
| 3–10 | Define the all-model family and its carrier convention | `Fix a consistent theory $T\supseteq\PA$. Let $\mathcal M_T$ be the set of all structures for th` |
| 12–23 | Define the product category and model functor | `Define the product category \[ \mathcal D_T=\prod_{M\in\mathcal M_T}\Pfn. \] An object is a fam` |
| 25–40 | State the result and begin its proof | `The functor $F_T$ is faithful and preserves restrictions, zeros, binary restriction products an` |
| 42–48 | Prove the preceding result / construction | `A restriction idempotent in $\mathcal D_T$ is a family of partial identities on subsets. Its sp` |
| 50–57 | Prove the preceding result / construction | `A partial monomorphism has injective coordinate functions: test its defining property on object` |
| 59–63 | Distinguish source and target connected domains | `For consistent computably enumerable $T\supseteq\PA$, the source $S_T$ is not locally connected` |
| 65–91 | Construct theory-extension functors and the commuting square | `For an inclusion $T\subseteq T'$ of consistent theories, define \[ Q_{T,T'}:S_T\to S_{T'},\qqua` |
| 95–123 | State the result and begin its proof | `Let $T\supseteq\PA$ be consistent. Fix $U=\omega$ and a Turing morphism $\tau:U\times U\rightha` |
| 125–136 | Show the interpreted Turing morphism is not universal | `The morphism $F_T(\tau_T)$ is not a Turing morphism in $\mathcal D_T$. Fix $M\in\mathcal M_T$. ` |
| 138–142 | Distinguish source conditionals from arbitrary target separators | `The target restriction lattices are Boolean, so every image of a disjoint source pair has a sep` |
| 147–170 | Define numeral observations and prove their equality criterion | `Suppose in addition that $T$ is computably enumerable. For a restriction idempotent $c=[C]_T$ o` |
| 174–184 | Give the complete-ambient-theory distinction | `For $T=\operatorname{Th}(\N)$, the identity-on-objects assignment \[ D:S_{\operatorname{Th}(\N)` |

`main.tex` supplies only the document/input order; `preamble.tex` supplies notation, theorem environments and metadata. Their functions have been checked without classifying package declarations as mathematical prose. Each bibliography item supplies attribution/source identification; all 31 entries were read, with factual verification reserved to the citation audit.

Inventory total: 363 substantive source paragraph groups.
