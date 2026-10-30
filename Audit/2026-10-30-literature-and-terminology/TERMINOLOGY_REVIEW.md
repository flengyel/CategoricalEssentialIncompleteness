# Terminology review: Version 3

The categorical exposition now uses **restriction idempotents** throughout. The abstract opens with categorical inseparability; essential incompleteness of PA is stated separately as a logical consequence. Partial identities are distinguished from the subsets or subdiagrams on which they are defined. The manuscript metadata reads Version 3, 30 October 2026.

## Outline and dependencies

The existing organization is retained:

| Part | Existing subsections and mathematical function |
| --- | --- |
| 1. Introduction | Di Paola–Heller problem, antecedents, contributions, roadmap |
| 2. Categorical preliminaries | Partial maps and restriction idempotents: definitions; products, coproducts, and local connectedness: structure; recursion categories: universal computation |
| 3. The syntactic recursion category | Uniform program equality, composition, ranges, Turing morphism |
| 4. Interpretation in models | Definition and structural preservation of each model functor |
| 5. A faithful family and theory extension | Faithful product interpretation and extension square |
| 6. Switching and the local-connectedness theorem | Local-connectedness construction; sufficient condition for lifting; lifting in the syntactic category; transfer from inseparable restriction idempotents to incompleteness |
| 7. Essential incompleteness of arithmetic | Numerical application and finite-proof inclusions; numeral instances and theory extension |
| 8. A recursion category from a three-point space | Construction; local connectedness and lifting; endpoint functors; proof observations and extensions |
| Appendix A | Cosheaves and numerical diagrams; partial maps, ranges, and connected restriction idempotents; universal object and frames; Turing morphism; recursion category and splitting |
| Appendix B | Syntax algebra; proof object and its range |
| Appendix C | Counterexample when section lifting is omitted |

The central dependency remains: local connectedness supplies the target sections; lifting the sections associated with complementary source restriction idempotents gives source inseparability; total inverse image transfers inseparability to the restriction idempotents representing theorems and refutations. Finite computation proofs supply the additional arithmetic inclusions. The general range functor is not required to preserve products.

## Principal repairs

| Anchor | Difficulty | Basis | Implemented repair |
| --- | --- | --- | --- |
| Abstract, first sentence | The logical consequence was presented as the categorical theorem | Explicit user correction; KLR §1, points 11–12, applied to distinguish the two claims | “We prove a categorical inseparability theorem for restriction idempotents in a recursion category.” A separate paragraph begins “As a logical consequence…” |
| Abstract and categorical statements throughout | Invented “computation domains” and older categorical “domain” synonym | Explicit user terminology; skill's context-sensitive vocabulary requirement | Restriction idempotents, restrictions, or an unambiguous antecedent |
| Preliminaries, partial functions, product-model proof, numerical and diagram applications | Idempotents were sometimes identified directly with their defining subsets | KLR §1, points 11, 14, 17; mathematical typing | Partial identities are the arrows; subsets and subdiagrams are their domains of definition or split objects |
| Theory-extension and proof-range passages | Closure and membership were ascribed directly to an idempotent | Explicit mathematical distinction between an arrow and its split subdiagram | Closure and formula membership are stated for split subdiagrams; the order on idempotents expresses inclusion |
| Headings and source metadata | Categorical synonym persisted in headings; old version remained | User correction and version task | Headings use restriction idempotents; Version 3 / 30 October 2026; unused `\Dom` macro removed |

No new outline is warranted. The largest changes are the abstract and the categorical terminology, not the proof organization.

## Definitions and notation

Section 2 explicitly defines restriction categories and restriction idempotents before their formal use in the later statements, followed by their order, disjointness, complementarity, inseparability, inverse image, range, and splitting. Local connectedness, sections, weak choice, Turing morphisms, and recursion categories remain defined in the preliminary section. The abstract and introduction preview these established concepts; no new shorthand or dictionary paragraph was introduced. Existing internal labels containing `domain` are retained so cross-references remain stable.

The stipulated lifting condition is unchanged: the target sections associated with complementary **source** pairs lift. No arbitrary target restriction idempotent or separator is required to lift. The source lift is not newly required to be total.

## Disclaimer and economy pass

A further complete-source pass follows the author's instruction to retain qualifications only when they bear on the results. The following were removed or consolidated:

- The preliminary paragraph about Heller's generation and iteration assumptions, including the denial that they presuppose a Turing morphism. The introduction retains the attribution through local connectedness. The adjacent sentence announcing that ranges and coproducts would be additional hypotheses was redundant with the definitions and statements.
- The reminder that the syntactic construction does not require c.e. axioms: the setup already quantifies over consistent extensions without that restriction.
- The general claim that faithfulness does not require source preimages of target idempotents. The preceding concrete source/target distinction remains.
- The retrospective audit of the source lift's possible partiality. The theorem still explicitly types the lift as partial and requires its image to equal the specified total target section.
- The sentence that the incompleteness corollary needs no closure rules: its hypotheses and proof already state exactly what is used.
- The clause about a representing program outside its source carrier, and the analogous clause about behavior outside the explicitly specified component domain. The definitions and exact-domain statement remain.
- The finite-valuation proof tail denying the need for a natural global valuation or separator. The proof already fixes a component, two proofs, and their finite atom set.
- The repeated lifting-verification paragraph following the nonnumerical-distinction proof. The main local-connectedness-and-lifting subsection contains the same argument.
- “The pointwise quotients do not give an alternative” was replaced by the actual fact: their proposed composition is not well-defined.

Retained qualifications concern actual mathematics used or compared: lack of product preservation for a general range functor, target sections only for complementary source pairs, the source/target separator distinction, the complete theory of the standard natural numbers, failure of central-component universality, the cosheaf product/subobject counterexamples, and the missing-lift counterexample. These are substantive failed implications or precise hypotheses, not anticipatory reassurance.

## Remaining occurrences of “domain”

All remaining occurrences are classified below. Line numbers identify the terminology-and-economy snapshot; source fragments remain identifying anchors if later additions shift the lines. No remaining occurrence uses “domain” as a synonym for a restriction idempotent.

| Line | Source fragment | Classification |
| --- | --- | --- |
| 127 | `Corollary~\ref{cor:domain-incompleteness} states this implication` | Internal label or cross-reference; unchanged, not rendered terminology |
| 142 | `Corollary~\ref{cor:domain-incompleteness} proves incompleteness of every` | Internal label or cross-reference; unchanged, not rendered terminology |
| 210 | `domain of definition and image, respectively.` | Set-theoretic domain of definition of a partial function |
| 282 | `partial inverse of an injection on its domain.` | Set-theoretic domain of definition of a partial function |
| 357 | `\begin{equation}\label{eq:domain-order}` | Internal label or cross-reference; unchanged, not rendered terminology |
| 395 | `on domains of definition and images. Restriction products are Cartesian products;` | Set-theoretic domain of definition of a partial function |
| 430 | `function's domain. Similarly,` | Set-theoretic domain of definition of a partial function |
| 779 | `\begin{corollary}\label{cor:domain-incompleteness}` | Internal label or cross-reference; unchanged, not rendered terminology |
| 822 | `splitting when applying Corollary~\ref{cor:domain-incompleteness}.` | Internal label or cross-reference; unchanged, not rendered terminology |
| 866 | `Corollary~\ref{cor:domain-incompleteness}. Work in` | Internal label or cross-reference; unchanged, not rendered terminology |
| 869 | `functions with c.e.\ domains in those carriers. A restriction idempotent` | Set-theoretic domain of definition or its c.e. membership test |
| 898 | `\begin{equation}\label{eq:arithmetic-domain-inclusions}` | Internal label or cross-reference; unchanged, not rendered terminology |
| 916 | `with \eqref{eq:arithmetic-domain-inclusions}, satisfies the hypotheses` | Internal label or cross-reference; unchanged, not rendered terminology |
| 917 | `of Corollary~\ref{cor:domain-incompleteness}. That corollary makes` | Internal label or cross-reference; unchanged, not rendered terminology |
| 1104 | `functions with c.e.\ domains contained in their sources.` | Set-theoretic domain of definition or its c.e. membership test |
| 1143 | `the functions $F(z,-)$, including their domain tests.` | Set-theoretic domain of definition or its c.e. membership test |
| 1161 | `the domain specified by the next partial function. This proves` | Set-theoretic domain of definition or its c.e. membership test |
| 1168 | `\begin{equation}\label{eq:probe-domain}` | Internal label or cross-reference; unchanged, not rendered terminology |
| 1284 | `Corollary~\ref{cor:domain-incompleteness}. Hence $t,\nu^*t$ are` | Internal label or cross-reference; unchanged, not rendered terminology |
| 1306 | `Corollary~\ref{cor:domain-incompleteness} then give the corresponding` | Internal label or cross-reference; unchanged, not rendered terminology |
| 1368 | `subdiagrams used as partial-map domains are categorical subobjects` | Actual c.e. subdiagram of definition or component subset |
| 1477 | `If $g:Z\rightharpoonup W$ has domain $D_g$, the domain of $gf$` | Actual c.e. subdiagram of definition or component subset |
| 1485 | `and identities follow from these domain and value formulas.` | Actual c.e. subdiagram of definition or component subset |
| 1490 | `splits through its domain subdiagram: the inclusion is total,` | Actual c.e. subdiagram of definition or component subset |
| 1491 | `and its partial inverse is the identity with that domain.` | Actual c.e. subdiagram of definition or component subset |
| 1492 | `Empty domains give restriction zeros. The restriction product` | Actual c.e. subdiagram of definition or component subset |
| 1494 | `the intersection of the two domains and has the ordered pair` | Actual c.e. subdiagram of definition or component subset |
| 1498 | `of the two domains. A product with an empty domain is empty,` | Actual c.e. subdiagram of definition or component subset |
| 1510 | `equality of domains.` | Actual c.e. subdiagram of definition or component subset |
| 1518 | `Intersections and finite unions of domain subdiagrams are again` | Actual c.e. subdiagram of definition or component subset |
| 1521 | `$e$ on $Z$ with domain subdiagram $D_e$, the inverse image $f^*e$` | Actual c.e. subdiagram of definition or component subset |
| 1530 | `and let $D_p$ be its domain subdiagram. If two elements of $(D_p)_j$` | Actual c.e. subdiagram of definition or component subset |
| 1537 | `The resulting partial arrow $s:Z\rightharpoonup Y$ has domain` | Actual c.e. subdiagram of definition or component subset |
| 1549 | `by two disjoint domain subdiagrams, the part containing its central` | Actual c.e. subdiagram of definition or component subset |
| 1560 | `the same for $f_1,g_1$ and $f_2,g_2$. Thus all three domains and all three` | Actual c.e. subdiagram of definition or component subset |
| 1593 | `letters belong to its domain, also letterwise. These formulas` | Actual c.e. subdiagram of definition or component subset |
| 1742 | `$\operatorname{encode}_{d_j}$-code. This function has domain` | Domain of a partial recursive component function |
| 1750 | `\qquad\text{with domain }D_j.` | Domain of a partial recursive component function |
| 1769 | `$\tau_i(c_i(y_i),v_i)$, for $v_i\in V_i$, has domain exactly` | Domain of a partial recursive component function |
| 1787 | `This proves equality of the central domains as well as their` | Domain of a partial recursive component function |
| 1788 | `values. Since $c\times1_V$ is total, the componentwise domain` | Domain of a partial recursive component function |
| 1823 | `domain inclusion and partial inverse. Send $(Y,e)$ to $D_e$` | Split subdiagram of definition or its inclusion |
| 1835 | `The domain subdiagram of $mm^\dagger$ is isomorphic to $Z$,` | Split subdiagram of definition or its inclusion |
| 2093 | `Let $(W_a^K)_{a\in\N}$ enumerate the domains of an acceptable` | Set-theoretic domain of an oracle-relative or ordinary partial function |
| 2101 | `domain $D_f$ is c.e.\ relative to $K$ and which has an ordinary partial` | Set-theoretic domain of an oracle-relative or ordinary partial function |
| 2116 | `Here $\simeq$ includes simultaneous undefinedness: the actual domain` | Set-theoretic domain of an oracle-relative or ordinary partial function |
| 2119 | `specified domain.` | Set-theoretic domain of an oracle-relative or ordinary partial function |
| 2137 | `extension $g_0f_0$ and domain` | Set-theoretic domain of an oracle-relative or ordinary partial function |
| 2141 | `This domain is c.e.\ relative to $K$: enumerate $D_f$, compute the` | Set-theoretic domain of an oracle-relative or ordinary partial function |
| 2149 | `their domains are respectively products and tagged unions of the given` | Set-theoretic domain of an oracle-relative or ordinary partial function |
| 2150 | `domains, and their extensions are the corresponding ordinary partial` | Set-theoretic domain of an oracle-relative or ordinary partial function |
| 2171 | `Its domain is c.e.\ relative to $K$, uniformly in all three` | Set-theoretic domain of an oracle-relative or ordinary partial function |
| 2176 | `partial recursive extension $V(z,x)$ and domain $D_v$ c.e.\ relative` | Set-theoretic domain of an oracle-relative or ordinary partial function |
| 2191 | `$v=\tau_K(r\times1_{\N})$, with equality of domains and values.` | Set-theoretic domain of an oracle-relative or ordinary partial function |
| 2259 | `and $i_0$, respectively. Their domains are disjoint. Any common` | Set-theoretic domain of an oracle-relative or ordinary partial function |

The inventory covers 55 source lines and 57 word occurrences. No remaining matches for “computation domain”, “restriction domain”, “theorem domain”, “domain joins”, “connected domain”, “complementary domain”, “least-domain”, or “inseparable domain” occur.

## Scope and verification

Read the complete 2,298-line starting source and made the complete-source terminology and disclaimer passes described above. Consulted the mathematical-writing skill and both supporting references, and the supplied KLR Section 1 excerpt, points 1–19 (printed pp. 1–3; PDF pp. 3–5). Only principles actually visible in that excerpt are attributed above; this is not a claim to have consulted all of KLR.

Automated comparisons confirmed all 49 labels, all 11 bibliography keys, and all 88 display-mathematics blocks unchanged. The economy pass removed one repeated Heller citation with its paragraph; no new citations were added. The theorem hypotheses, lifting condition, product-preservation distinction, and logical/categorical separation are retained. Compilation and rendered-page inspection are assigned to the coordinating agent and are not claimed here.
