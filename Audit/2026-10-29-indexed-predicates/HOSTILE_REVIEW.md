# (A) Kill-shots / hard blockers

No confirmed fatal or major mathematical blocker was found in the current note. This is an author-side audit, not a journal referee report or a certification of correctness or novelty. The reviewed artifact is *Definability over a recursion category*, dated 29 October 2026: the entire 367-line LaTeX source and all five pages of the corresponding PDF. Page numbers below are the printed PDF page numbers; source lines refer to this pre-revision snapshot.

The central claim is conditional: if every complementary computational-domain pair is represented by total substitution, then the distinguished predicates have no complementary computational-domain separator. The numerical interpretation identifies that representation condition with strong numeralwise definability. The note does not assert that recursion-category structure alone supplies representation.

The actual outline and dependency order are:

| Section | Function | Principal dependency |
| --- | --- | --- |
| 1. Computations and their domains | Defines the partiality framework, total maps, binary restriction products, domain lattices, and inverse image. | Restriction axioms, restriction zeros, stable finite domain joins. |
| 2. An indexed lattice of predicates | Defines the second doctrine and domain embedding; gives the Grothendieck fibration. | Two contravariant bounded-distributive-lattice functors and naturality. |
| 3. Substitution and representation | Defines total substitution and existential representation; separates external choices. | Products in the total-map category and predicate inverse image. |
| 4. Inseparability | Proves Theorem 4.1 by a diagonal complementary pair. | Representation, naturality, injectivity, totality, and unequal domain bounds. |
| 5. Extensions and the numerical interpretation | Proves Corollary 5.1 and the arithmetic consequence. | Represented disjoint extensions, coding, consistency, and strong numeralwise definability. |
| 6. Morphisms and chosen operations | Specifies variance, compatibility, and preservation of representatives. | Restriction/product-preserving functors and natural predicate maps. |

No alternative outline is warranted for this five-page note. The definitions precede the proof steps that use them, and the numerical interpretation follows the abstract result.

# (B) Major weaknesses

None confirmed. In particular, the following potential objections were checked and do not furnish major findings:

| Claim and anchor | Typed signature / law checked | Derivation or test | Status |
| --- | --- | --- | --- |
| Domain inverse image, p. 1, §1, lines 63–86: “Thus $E:\mathcal{C}^{op}\to\mathbf{BDLat}$ is a functor.” | For total $f:X\to Y$, $f_E^*:E(Y)\to E(X)$, $e\mapsto\overline{ef}$. | Restriction gives meet preservation and contravariant composition. Totality gives preservation of top; restriction zeros give bottom; join stability is separately assumed. | Checked. Partial arrows are not silently treated as bounded-lattice maps. |
| Predicate embedding, p. 2, §2, equation (1), lines 102–113. | $j:E\Rightarrow P$; $f_P^*j_Y=j_Xf_E^*$. | Injectivity of a lattice homomorphism reflects order because $j(a)\le j(b)$ implies $j(a\wedge b)=j(a)$, hence $a\wedge b=a$. | Checked. The requested functor-category formulation below is equivalent. |
| Fibration, p. 2, §2, lines 115–129. | $(X,p)\to(Y,q)$ is $f:X\to Y$ with $p\le f^*q$; projection to $\mathcal{C}$. | Composition follows from $p\le f^*q\le f^*g^*r=(gf)^*r$. A map over $fk$ factors uniquely through $(X,f^*q)\to(Y,q)$, because its condition is $p\le k^*f^*q$. Identity/composition of chosen lifts follow strictly from functoriality. | Checked. This is an ordinary split fibration with poset fibres. |
| Induced domain-to-predicate functor, p. 2, §2, lines 128–129. | $\int E\to\int P$, $(X,e)\mapsto(X,j_Xe)$, with the same underlying arrow $f$. | Monotonicity and naturality send $e\le f_E^*d$ to $j_Xe\le f_P^*j_Yd$. Naturality also preserves the specified cartesian lifts. | Checked. |
| Representation, p. 3, Definition 3.1, equation (2), lines 148–179. | $g:U\to U$ is total; $c_g=s(g\boxtimes1_U):U\boxtimes U\to S$; both equations belong to $P(U\boxtimes U)$. | $\operatorname{Rep}\to\operatorname{Comp}(E(U))$ is surjective exactly when witnesses exist. A chosen section is an external set function. The proof below uses one existential witness, not a computable selector. | Checked. |
| Theorem 4.1, pp. 3–4, lines 198–251. | Separator domains are on $S$; their swapped inverse images under $\delta=s\Delta_U$ are on $U$. | The representative $g$, $\gamma=\langle1_U,g\rangle$, and $t=\delta g$ satisfy $c_g\gamma=t$, $\pi_2\gamma=g$. Pullback of representation and separation yields both inequalities between $j_U(t^*d_+)$ and $j_U(t^*d_-)$. Injectivity identifies complementary domains, contradicting $0_U\ne1_U$. | Checked. No global element, terminal object, or monoidal unit is used. |
| Corollary 5.1, p. 4, lines 257–271. | $b_+,b_-\in E(S)$; their images extend $p_+,p_-$ and are disjoint. | If their image join were top, preservation and injectivity of $j_S$ would reflect both complement equations. Theorem 4.1 excludes the resulting separator. | Checked. |
| Arithmetic adequacy, pp. 4–5, §5, lines 281–307. | A total two-variable substitution function, unary-formula enumeration, and sentence enumeration; $p_\pm\subseteq\mathbb{N}$. | A strong definition gives constant total $g(x)=a$. Consistency turns the two numeralwise implications into exact preimage equalities. Conversely evaluate a representing total $g$ at the ordinary number $0$. This evaluation occurs only in the numerical model. | Checked, subject to the local coding clarification in (C). |
| Arithmetic consequence, p. 5, §5, lines 309–315. | Explicit hypothesis that every recursive set is strongly definable in consistent $T$; consistent c.e. deductive extension $T'$. | The theorem/refutation supports of $T'$ are c.e., extend those of $T$, and are disjoint. Corollary 5.1 excludes their covering all sentence codes. Surjectivity of the sentence enumeration makes this exactly incompleteness. | Checked. No c.e. hypothesis on $T$ is introduced. |
| Structure morphisms, p. 5, §6, lines 325–350. | $F:\mathcal{R}\to\mathcal{R}'$, $F_t:\mathcal{C}\to\mathcal{C}'$, and $\eta:P\Rightarrow P'F_t^{op}$. | $E(F)_X(e)=F(e)$ preserves domains, lattice operations, and inverse image. Naturality of $\eta$, the compatibility $\eta j=j'E(F)$, preservation of $s$, and product preservation transport each representation equation to $F(g)$. Composition is $G F$ with component $\theta_{F X}\eta_X$. | Checked. Variance is correct. Noninjective $\eta_X$ is allowed and causes no claimed reflection. |

The two-object, one-arrow test was applied to the indexed-lattice and fibration constructions. With base $A\to B$, constant $E=\mathbf{2}$, $P(A)=\mathcal{P}(\{0,1\})$, $P(B)=\mathbf{2}$, and inverse image sending the bounds to the bounds, the domain embedding and cartesian lifts work without an inverse arrow $B\to A$. No argument is restricted accidentally to isomorphisms.

# (C) Minor issues

## C1. The numerical product encoding should be declared

- **Anchor:** p. 4, §5, lines 273–287: “objects are infinite recursive subsets of $\mathbb{N}$” and “$s:\mathbb{N}^2\to\mathbb{N}$.”
- **Claim as written:** This numerical category is a concrete instance, and the displayed two-variable substitution is its total substitution arrow.
- **Failure mode:** `missing_definition`.
- **Why it needs repair as written:** The announced object collection contains subsets of $\mathbb{N}$, whereas the displayed ordinary set $\mathbb{N}^2$ is not literally one of those objects. The recursive coding that realizes restriction products in this presentation is not stated. This is a local omitted identification, not a counterexample to the theorem.
- **Evidence:** `absence_in_text` and `structural_argument`: no pairing bijection or transported product carrier is specified in the complete source; a fixed recursive pairing supplies the required typed identification.
- **Missing datum:** A recursive bijection $\langle-,-\rangle:\mathbb{N}^2\cong\mathbb{N}$, and the convention that products and two-variable computations are transported through it.
- **Downstream impact:** The connection between the ordinary function $s(a,n)$ and the categorical arrow $U\boxtimes U\to S$ is not explicit.
- **Severity:** minor.
- **Repairability:** local, without changing a hypothesis or conclusion.
- **Recommended repair:** “Choose a recursive bijection $\langle-,-\rangle:\mathbb{N}^2\cong\mathbb{N}$ and use it to encode products. We write $s(a,n)$ for the substitution map in decoded coordinates.”
- **Editorial basis:** *Mathematical Writing*, §1, point 11, requires variables to be introduced at least informally; its complementary-explanation advice and the skill's explicit-typing convention support making this identification visible. The precise categorical repair is an independent mathematical judgment.

## Requested categorical formulation of $j$: equivalent clarification, not a defect

At p. 2, §2, lines 102–113, the existing componentwise definition is correct. The requested replacement can be stated without strengthening it:

> Supply a monomorphism $j:E\hookrightarrow P$ in the functor category $[\mathcal{C}^{op},\mathbf{BDLat}]$. Equivalently, each component $j_X:E(X)\to P(X)$ is an injective bounded lattice homomorphism; in particular, each $j_X$ is an order embedding.

The equivalence follows because finite limits in the functor category are computed componentwise, and a map is monic exactly when its diagonal into its self-pullback is invertible. Monomorphisms in $\mathbf{BDLat}$ are precisely injective homomorphisms: noninjectivity is detected by two homomorphisms from the free bounded distributive lattice on one generator. This justification concerns ordinary categories, not an enrichment base.

## Role of $(\mathscr{V},\times,1)$: no such extra datum in this note

The audited text never introduces $\mathscr{V}$, an enrichment tensor, or its unit. Its products are binary restriction products in $\mathcal{R}$, which become ordinary binary products in $\mathcal{C}=\operatorname{Tot}(\mathcal{R})$. Its symbols $1_X$ and $1\in P(X)$ denote an identity arrow and a lattice top, respectively. They are not terminal objects. This is a confirmed distinction, not a missing assumption.

The theorem can be described using ordinary functors and a fibred predicate lattice. Reintroducing an enrichment base is unnecessary for any proof in the note. Ordinary Set-valued homsets in the surrounding mathematics do not assert computability of a choice of representatives.

# (D) Cross-section consistency failures

No cross-section inconsistency was confirmed. The following checks specifically address earlier risks:

1. **The previously missing arithmetic premise is now present.** On p. 5, §5, lines 309–310, the note says, “Assume now that every recursive set is strongly definable numeralwise in $T$.” This is the evidence that resolves the earlier omission. The subsequent argument is not being silently repaired by the abstract.
2. **The unqualified essentially-algebraic classification is absent.** Page 3, §3, lines 181–187 only lists chosen operations and the equational domain of $\rho$. It does not claim a free adjunction or a classification of the full structure, including injectivity and nondegeneracy. Page 5, §6 correctly warns that choice-preserving morphisms define a different category.
3. **Unused Turing structure is disclosed.** Page 4, §4, lines 244–251 explicitly states that the proof works for the weaker indexed-lattice data and does not use universal application again. This is a legitimate stronger theorem, not a hidden inference from Turing universality. No artificial use of an unused hypothesis is needed.
4. **The global disjointness hypothesis is not used in the final diagonal calculation.** It remains meaningful in the intended representation data and follows from consistency in the arithmetic model. Keeping it is harmless. The note's weaker-data observation should not be read as claiming that every listed premise is individually necessary.
5. **Existence and effective selection remain distinct.** Page 3, §3 says expressly that $\rho$ is an ambient set function, not a morphism of $\mathcal{R}$. No equation later requires a computable extensional selector.
6. **The numerical model in this note is a powerset doctrine.** Page 4, §5, lines 273–279 says so explicitly. Page 5, lines 319–321 treats subobject realizations as additional constructions. The note does not assert that the full PER-subobject lattices in the existing Lean development equal these powersets, and makes no claim that this exact numerical powerset presentation has been formalized.
7. **No quotient-completion claim is imported.** Corollary 5.1 is about disjoint represented predicate extensions. The arithmetic application does not claim a constructed Lindenbaum Boolean presentation or an identification of all theory extensions with Boolean quotients.

Definition and equality audit: categorical morphism equality is ordinary equality in the declared categories; numerical morphisms are partial functions, not program indices. Formulas and sentences are indexed syntactic objects in §5. The value $g(0)$ is a numeral returned by a total recursive function and serves as a formula code. Domains are restriction idempotents, and only their numerical supports are identified with sets. No conflation of these equality notions was found.

Small tests: the one-point degenerate restriction category is excluded by $0_U\ne1_U$. The restriction monoid $\{0,1\}$ on a one-point set confirms the zero/top and complement calculations, but it has no Turing morphism indexing both maps, so it is not a counterexample to the recursion-category premise. In the weaker ordinary-category version, a terminal base with constant lattice $\mathbf{2}$, $j=1$, and distinguished pair $(1,0)$ represents only that pair with its sole arrow; it fails universal representation and therefore does not refute the theorem. These tests expose the roles of nontriviality and representation rather than circumventing them.

# (E) Acceptance conditions, non-negotiable

No major reconstruction or mathematical rejection condition is justified by the evidence gathered. The following are the verifiable endpoints for the requested revision, rather than grounds for inventing a stronger theorem:

1. **Make the numerical coding identification explicit.** Deliverable: the one-sentence pairing convention in §5, with the substitution arrow still typed $U\boxtimes U\to S$. Endpoint: the specified object class and the displayed numerical input agree under the declared coding. If unmet, retain C1 as a minor qualification; do not characterize the numerical presentation as fully explicit.
2. **Use the requested categorical formulation of $j$.** Deliverable: $j$ stated as a monomorphism in $[\mathcal{C}^{op},\mathbf{BDLat}]$, followed by the equivalent componentwise order-embedding description. Endpoint: naturality equation (1), Theorem 4.1, and Corollary 5.1 retain exactly their existing hypotheses and proof. If unmet, the user-requested terminology change is incomplete, not the existing mathematics false.
3. **Preserve the verified scope.** Deliverable: keep the explicit strong-definability premise in §5, the unequal-bounds premise in Theorem 4.1, and the external status of $\rho$. Endpoint: no arbitrary consistent theory is claimed essentially incomplete, and no computable selector is claimed. Deleting one of these distinctions would require a new mathematical review and may invalidate the corresponding claim.
4. **Verify the revised rendered artifact.** Deliverable: compile the exact revised source and inspect its pages, references, and diagram. Endpoint: no unresolved references or clipped diagram/text. The present source/PDF were read and visually inspected, but this audit does not certify a later revision.

# (F) Not checked / uncertainty log

- The entire note and all five PDF pages were reviewed. The PDF's equations, diagram, and text were legible; no clipping or unresolved printed reference was found. The corresponding numerical implementation and its source hashes were not rebuilt during this manuscript audit.
- The supplied *Mathematical Writing* was consulted in §1, especially points 5, 10–17, 24, and 26, and §§4–5 on contextual placement of definitions. Printed pages 1–5 and 9–11 were used. Its advice supports explicit hypotheses, introduced variables, coherent notation, and connected prose; it does not certify mathematical correctness or prescribe this report's A–F organization.
- Cockett–Lack's primary PDF was inspected for the restriction axioms and the §4 discussion of fibred semilattices. The manuscript's references to those topics are supported. Source: https://cspages.ucalgary.ca/~robin/FMCS/FMCS_06/RestrictionsI.pdf . The full Heller PDF was not independently reread in this audit. The companion source audit, reported by the coordinating author-side reviewer, verified §3 p. 1256 for isotypes, §5 pp. 1260–1261 for the prodominical convention, and §9 pp. 1264–1265 for Turing morphisms and recursion categories. This review independently verified the publisher's bibliographic record and abstract, not those full pages. Source: https://doi.org/10.2307/2274486 .
- No historical novelty or priority claim is asserted by the note, and no exhaustive literature comparison was attempted. The abstract proof's value or suitability for a particular journal cannot be inferred from this correctness audit.
- The full powerset doctrine is a sound mathematical instance of the displayed assumptions. Equivalence to a full PER-subobject doctrine is neither established here nor needed; no such equivalence should be inferred from the existing Lean work.
- This audit does not establish that the entire historical Di Paola–Heller program is complete, nor that the arithmetic consequence is a special case of a constructed Lindenbaum quotient theorem. The present note does not make either claim.

**Resolution addendum, source-only check after the author-side revision.** The revised source has 359 lines. Lines 244–266 now explicitly choose a recursive pairing, transport products through it, state extensional equality of numerical arrows, and identify the displayed two-variable substitution with a total categorical arrow. C1 is resolved in source. Lines 105–122 state the requested monomorphism in the functor category, its equivalent componentwise order-embedding property, and the correctly typed naturality square. Lines 58–59 add the pairing uniqueness equation, making the product assertion explicit. The strong-definability premise remains at lines 288–289; the proof is unchanged in mathematical content. The external choice of representatives is moved after the proof, to lines 319–346, and remains expressly nonalgorithmic. No enrichment base has been introduced. These observations are based on reading the revised source; the original five-page PDF inspection above is not an assertion that the revised PDF was inspected. The coordinating reviewer is responsible for compiling and checking the revised rendered artifact.

**Final self-audit.** Strongest confirmed blocker: none. Strongest confirmed defect in the original input: the minor undeclared numerical product coding in C1, now resolved in the revised source. Strongest suspected unconfirmed blocker: none identified; unavailable independent rereading of the cited Heller sections is a source-verification limitation, not evidence of a false theorem. Most important thing not checked: an independently verified correspondence between this exact powerset presentation and any claimed formal implementation, and a complete literature assessment of the note's research contribution. The proof assessment does not depend on unavailable material beyond the standard categorical assumptions explicitly stated; the historical-source assessment partly uses the companion audit. **Final recommendation: unknown.** No fatal or major mathematical defect was established, and there is no evidence-based reason to manufacture a rejection; publication-level novelty and significance were not assessed.
