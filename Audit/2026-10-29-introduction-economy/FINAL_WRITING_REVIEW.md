# Complete-source writing audit of version 2

The current source has a coherent definition section and substantially clearer types than its predecessor. The remaining substantial exposition defect is the dependency of the incompleteness applications on the local-connectedness theorem: the abstract conflates the model-family application with the numerical application, and the three-point discussion changes its chosen pair before proving incompleteness. These are concrete dependency issues, not objections to category-theoretic terminology itself.

Reviewed source: `manuscript/essential_incompleteness_via_local_connectedness_v2.tex`, title *Local connectedness, range functors, and essential incompleteness*, visibly marked Version 2, 29 October 2026. The source was read continuously from preamble through bibliography, including all three appendices. Its hash at completion of the first reading was `7d134f58d42e86728f8d9ddeeefbe4dd8269d24e9086171d55dae5155d6af288`. The root agent is revising the source concurrently; the findings below describe that reading and must be checked against the final revision.

The mathematical-writing skill and both supplementary reference files were read. The locally supplied extract of Knuth, Larrabee, and Roberts, *Mathematical Writing*, covers Section 1, points 1–19, printed pages 1–3 (PDF pages 3–5). Verified principles used here are self-contained theorem statements (point 5), connected exposition (10), explanation and variables at first introduction (11), reader motivation (12), prose intelligible when formulas are skimmed (13), consistent notation (14), and unambiguous reading from left to right (17). Attempts to retrieve the complete official Stanford PDF and bibliography page timed out. No claim is made to have verified points 24 or 26 or Sections 4–5; suggestions about avoiding local jargon and imposing definition order beyond those verified points are editorial applications of the user's instructions and the skill's supplementary conventions.

## Actual outline and dependencies

| Part | Function | Main dependencies and result |
|---|---|---|
| Abstract | State the result and applications | Essential incompleteness, faithful model interpretation, numerical proof enumeration, three-point construction. Its causal wording needs correction. |
| 1. Introduction | Problem, history, theorem overview, applications | Di Paola–Heller program; Rosolini/Heller/Lengyel with errata; Bernardi; range-functor lifting; exclusions of primed syntactic systems; arithmetic and three-point applications. |
| 2. Categorical preliminaries | Definitions | 2.1 partial maps, domains, range and splitting; 2.2 products, coproducts, range functors, connectedness, weak choice; 2.3 recursion categories and Turing morphisms. |
| 3. The syntactic recursion category | Construction and prior-work distinction | Uniform graph equality defines `S_T`; composition is well-defined; domains, ranges, products, coproducts and Turing morphism exist. Pointwise equivalence is distinguished explicitly. |
| 4. Interpretation in models | Construction and preservation | Typed object and arrow actions of `F_M`, including its particular preservation of products. |
| 5. A faithful family and theory extension | Representation theorem and comparison | Product target; faithful `F_T`; target local connectedness; quotient functors and projection square for theory extension. |
| 6. Switching and the local-connectedness theorem | Main categorical proof | 6.1 connected-domain argument, unique section and range-functor lifting theorem; 6.2 disjoint-join criterion; 6.3 uniform program lift and inseparable syntactic domains; 6.4 abstract theorem-domain corollary. |
| 7. Essential incompleteness of arithmetic | Application | `J:Rec→Pfn` produces numerical inseparability; finite PA proofs give domain inequalities; proof conclusions give theorem domains; completeness gives complementary pullbacks. Subsection records natural monotonicity under extension and the `S_T` observation equations. |
| 8. A recursion category from a three-point space | Construction and second application | Explicit category of numerical diagrams, partial-map category, universal object, full recursion subcategory; local connectedness/lifting; component functors; syntax and proof domains; endpoint inseparability and essential incompleteness. |
| Appendix A | Detailed construction proofs | Cosheaf equivalence; regular/extensive total category; partial maps and ranges; connected domains; universal object and isomorphisms; Turing morphism; restriction splitting and nonnumerical invariant. |
| Appendix B | Syntax, derivations and consistency | Initial finite-tree algebra; c.e. proof carriers; conclusion range; least rule closure; finite Boolean valuation argument. |
| Appendix C | Necessity of a named hypothesis | Explicit counterexample to Theorem `thm:local-lifting` with its section-lifting hypothesis omitted. |

No large reorganization is warranted. Keep the general domain-incompleteness corollary immediately after the lifting applications, and state both applications as explicit uses of it. Keep the lifting criterion and its proof in the body and all needed private-note arguments in the appendices.

## Findings and exact repairs

| Anchor | Actual difficulty | Basis | Recommended action |
|---|---|---|---|
| Abstract, “For the arithmetic application … apply it to this functor. Finite computations then …” | The prose makes `F_T` appear to supply the pair used in the proof of PA essential incompleteness. The actual proof invokes `J:Rec→Pfn`. | KLR 10, 12, 13; proof-dependency consistency. | Name the numerical application first and describe the faithful model-family construction as another application. State the theorem-domain pullback implication directly. |
| Introduction, final part of three-point paragraph, “it sends the chosen pair” | The nearest named pair is the one supplied by the range-functor theorem, but §8.3 replaces it by the inverse images of ranges of two global points. | KLR 11, 14, 17; definite antecedent. | Prefer one pair throughout. A possible mathematical repair is to use the complementary domains obtained from the coproduct isomorphism, then use the same domains for atomic axioms and endpoint observations. The root mathematician should verify this before implementation. Otherwise specify the two pairs and explain the bridge; do not retain “the chosen pair.” |
| §8.3, definitions of `q_j,a,b` | The second pair is proved inseparable directly by an endpoint self-application argument; the preceding local-connectedness application is then not used for essential incompleteness. | Mathematical dependency issue, separate from style. | With the explicit coproduct frame `b:V→V+V`, take `q_0=b^{-1}(1_V+0_V)b`, `q_1=b^{-1}(0_V+1_V)b`, and `a=(τΔ)^*q_0`, `b_1=(τΔ)^*q_1` (choose nonconflicting notation). The endpoint carriers become the even/odd first-output-coordinate sets. Then the categorical corollary applies directly and the endpoint theorem supplies additional effective observations. |
| Introduction, “Sections … develop the arithmetic application” | It hides that the faithful family is a separate syntactic application, while numerical theorem domains establish PA incompleteness. | KLR 12–13. | “Sections … construct the syntactic model functors and prove the lifting theorem. Section … derives arithmetic essential incompleteness from its application to the classical recursion category.” |
| First use of “nonnumerical recursion category” | Its intended meaning is proved later but never given at the first use. “Nonnumerical” could mean many different things. | User's antecedent instruction; explicit meaning. | “We also construct a recursion category not equivalent, as a restriction category, to the classical recursion category.” Thereafter “nonnumerical” has an antecedent if retained. |
| Proposition `prop:endpoint`, opening of second proof paragraph | `encode_2` and `decode_2` appear after only “Fix a recursive tuple coding”; their named definitions occur much later in Appendix A. | KLR 11, 14. | “Fix a recursive bijection `encode_2:N^2→N` with inverse `decode_2`, and an acceptable numbering `(φ_p)_{p∈N}` of the partial recursive functions.” |
| Same proof, “a total-on-Z recursive index map” | An unnecessary compound phrase obscures the distinction between an ambient recursive function and an arrow defined on a c.e. carrier. | User's terminology instruction and typing. | “Specialization gives a recursive index map defined at every element of `Z` for the partial functions `F(z,-)`.” If global totality is needed, introduce the ambient numerical power and specialization of the partial recursive extension explicitly. |
| Appendix A, Proposition `prop:fork-total` | “Regular,” “extensive” and “regular images” first occur in the theorem; these are standard category-theoretic terms, but their intended properties are only described in the proof. | Optional self-containedness improvement under the user's strict definition requirement; not invented terminology or a theorem defect. | Before the proposition: “A category is regular if it has finite limits and pullback-stable factorizations as a coequalizer of a kernel pair followed by a monomorphism. It is extensive if taking coproducts induces equivalences `E/A × E/B ≃ E/(A+B)` and `E/0` is terminal.” The proof then verifies these assertions. If treating these as assumed standard category theory, state that scope rather than inventing a missing-definition finding. |
| Proposition `prop:fork-recursion`, “full partial subcategory” | “Partial” adds no distinct definition to “full subcategory of the partial-map category A.” | Economy. | Use “full subcategory.” |
| §8 conclusion after Theorem `thm:cosheaf-observation` | The opening recap repeats the proved endpoint application. The sentence “one would need a functor …” sounds necessary for every other approach, while it is sufficient for this particular method. | KLR 13, 17; logical strength of wording. | Either delete the redundant recap, or retain a precise sufficient extension: “The same argument applies to another recursion category whose restriction splitting admits such a functor and corresponding domain inequalities.” State preservation of the particular inseparable pair if this sentence is retained. |

## Definition and notation inventory

| Term or symbol | First explanation / definition | Status |
|---|---|---|
| Essential incompleteness | Introduction, first paragraph | Explicit; abstract should give the short extension formulation if it is to stand independently. |
| Recursive separator / recursively inseparable | Abstract and introduction | Explicit, correctly distinguishes disjoint c.e. sets and a recursive separator. |
| Recursion category | Literature preview in introduction; formal definition §2.3 | Appropriate standard preview; no invented shorthand. |
| Range functor | Introduction explains preserved structure; §2.2 formal definition | Defined before technical use. Product preservation is explicitly excluded from its definition. |
| Restriction category, `bar f`, total map | §2.1 | Explicit typed axioms. |
| Domain order, meet, join, restriction order | §2.1 | Explicit before first proof. |
| Inseparable domains | §2.1 | Explicit separator formulation. |
| `f^*a`, range, agreement law | §2.1 | Defined with arrow types. |
| Split and restriction splitting | §2.1 | Explicit objects, arrows, identities and totality. |
| Restriction products, pairing and `Δ` | §2.2 | Defined. “Diagonal” is used for this map, not as the forbidden proof label. |
| Restriction coproduct, copairing, codiagonal | §2.2 | Explicit. |
| Coproduct comparison `χ` | §2.2 | Typed canonical isomorphism; named again in the lifting statement. |
| Connected domain / locally connected | Introduction gloss; §2.2 definition | Adequate. The definition includes the zero domain without falsely asserting nonemptiness. |
| Partial monomorphism, section, weak choice | §2.2 | Nonstandard partial-section convention is explicitly defined. |
| Prodominical, isotypical, Turing morphism | §2.3 | Formal definitions precede use. |
| Formal numerical type `ω`, graph `G_e` | §3 | Introduced before quotient construction. |
| `S_T`, `[e]_T`, `[C]_T` | §3 | Defined with representative/equality distinction. |
| `Pfn` | Introduction; explicit definition §§2 and 4 | Defined before first body use; repeated definition in §4 is brief and functional. |
| `F_M`, `M_T`, `D_T`, `F_T`, `Q`, `π` | §§4–5 | Object and arrow actions given. Particular product preservation is not conflated with the general range-functor definition. |
| Lifting hypothesis | Introduction overview; Theorem `thm:local-lifting` | Exact arrow and equation, with named theorem in Appendix C. No dangling “lifting hypothesis dropped” remains. |
| Theorem domains `t_T`, `ν`, `θ`, `Prf_T` | §7 | Defined before the corollary; the actual c.e. proof carrier and conclusion map are provided. |
| `Pair(Rec)` | §7.1 | Objects and arrows explicitly defined; identity and composition stated. Consider saying “c.e. subsets representing domains” to avoid switching between subsets and partial identities. |
| Set-valued cosheaf | §8 opening | Variance and coequalizer condition given before the three-point use. |
| `C_rec`, `E`, c.e. subdiagram | §8 opening | Explicit carriers and functions total on their c.e. source carriers. The former imprecise phrases have been removed. |
| `Par(E,Mono)` and `A` | §8 opening | Spans, monic leg, equality and composition explained. |
| Universal object, frames | §8 opening | Both explicitly defined. “Frames” is unnecessary additional terminology but not undefined or demonstrably invented; replacing it with “chosen isomorphisms” is optional economy. |
| `R_X` | §8 opening | Full subcategory specified and recursion-category claim supported by Appendix A. The whole cosheaf category is not called a recursion category. |
| Endpoint functors `E_j` | §8.2 | Typed object/arrow actions given. `E_0` is included explicitly although only `1,2` are endpoints. |
| Endpoint probe `H_i`, `Φ_i`, observed carrier | §8.2 | Explicit mathematical definitions and functoriality proof; these are not undefined informal metaphors. |
| Global point and `q_j` | §8.3 | Defined, but their replacement of the earlier pair creates the dependency problem listed above. |
| Polynomial functor `P`, initial algebra, atom map | §8.3 | Formula and universal property precede use. Detailed finite-tree construction is in Appendix B. |
| Theory extending `t_0`, consistency, completeness | §8.3 | Defined as domain equations and closure under the displayed rules. |
| Total restriction embedding | Appendix A.3 | Defined before lemma. |
| `Y^#` and free semigroup | Main text gives word carriers; Appendix A.3 gives functor and universal property | Adequate. Standard semigroup terminology can remain assumed. |
| Acceptable numbering and `≃` partial-value equality | Appendix A.4 | Specialization property and undefinedness convention are explicit before their detailed use. The earlier use of tuple-coding names needs the local repair above. |
| Decidable equality | Proposition `prop:fork-distinction`, proof | Its precise morphism-and-pullback meaning follows immediately; move the sentence just before the proposition if enforcing literal definitions before every statement. |
| Relative c.e. domains, `K`, `W_a^K` | Appendix C | Defined before counterexample construction. |

## Paragraph-function and antecedent pass

Every paragraph in the source performs one of these functions: definition; theorem/proof; construction; prior-work relationship; distinction needed for a subsequent inference; example or counterexample; proof dependency; or mathematical extension question. No paragraph narrates an LLM workflow or review procedure. The final three-point recap is the only clear candidate for removal on repetition grounds; the final source-observation warning using `Th(N)` is substantive because it prevents conflating semantic representation with an effective theorem enumeration.

The introduction currently has seven paragraphs. Their functions are, respectively: incompleteness problem; literature; exact range-functor hypothesis; syntactic application and exclusion of primed systems; arithmetic dependency; three-point construction; roadmap. This organization is motivated. It can be shortened by moving the displayed typing of `s_c` and `ell_c` out of the introduction, where the exact statement is already referenced, but that is optional: the typing now repairs a prior real ambiguity. Do not delete the explanation of what must lift or the relation to essential incompleteness.

Specific antecedents now present and worth retaining: “the section” refers to Proposition `prop:local-switch`; `χ` is the canonical coproduct isomorphism; “the lifting hypothesis” is tied to Theorem `thm:local-lifting`; “the source” and “the target” have the functor `F:R→A` in scope; “uniform” refers to one universally quantified graph-equivalence sentence; “component” refers to a named vertex of `J`; “the finite valuation” refers to the two proof trees just fixed. The unresolved “chosen pair” in the introduction is identified above.

Searches found no occurrences of “computable diagram,” “computational cosheaf,” “diagonal proof,” `LOCOct10f`, private range-completion filenames, `LLM`, `reviewer`, or `audit` in the mathematical source. The explanation that general range functors need not preserve products is supported by an explicit example; the distinct product-preservation claims for `F_M`, `F_T`, and `E_j` are individually stated and proved.

## Scope and final check required

This is a complete-source editorial reading with selected mathematical dependency checks, not an independent certification of every theorem or reference. The cited papers were not reverified during this writing pass. The full Stanford source was unavailable, while the supplied Section 1 extract was read and used as stated above. No final PDF was compiled or visually inspected by this subagent; the parent owns the exact-source build and final-page check. Re-read the final abstract, introduction, arithmetic corollary, and three-point pair after the concurrent edits, and confirm that both applications visibly depend on the local-connectedness theorem through the domain-incompleteness corollary.

### Follow-up reading after the root revision

The revised abstract, introduction, general domain corollary, arithmetic application, and three-point pair definition were read after the root's edits. The abstract was then edited directly under the root's limited authorization. It now explains local connectedness at first mention, describes recursive inseparability before using the word “separator,” and distinguishes the numerical proof from the model-family construction. Its lifting requirement is expressly limited to target maps associated with complementary source domains. The introduction now defines “nonnumerical” by restriction nonequivalence and identifies the pair used for the propositional atomic axioms. The three-point application uses the same parity pair produced by the local-connectedness theorem, and its proof invokes the general domain-incompleteness corollary before deriving the endpoint observations. These changes resolve the principal dependency and antecedent findings in the first table. The named tuple codings are now introduced before their first formula. The root owns any remaining optional background definitions and final rendered-page inspection.


## Final delivery disposition

The delivered source has SHA-256 `afa9ea49e8de7aeaae35b0ba430edab9aaaf04b2fcc36c476c4b7793fac17171`. The parent checked the final local wording changes, compiled that exact source, and inspected the principal rendered pages. See [the completion record](README.md) for the final theorem dependencies and checks. The earlier snapshot findings above are retained as review history; the confirmed dependency and definition-order repairs are implemented.
