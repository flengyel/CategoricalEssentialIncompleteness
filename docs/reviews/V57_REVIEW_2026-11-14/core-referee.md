# Core mathematical audit — manuscript v57

Pinned source: `dfe6d3b9b948875d9d268ef8bbd332d65c6b53e5`. Scope: §§2–5 and Appendix A. This is an author-side mathematical audit, not a journal referee report.

(A) Kill-shots / hard blockers

No confirmed hard blocker was found in the assigned material. In particular, the proof of Lemma 5.1 supports the required quantification over arbitrary slice computations. This conclusion comes from the constructions below, not from the recorded Lean status.

(B) Major weaknesses

No confirmed major mathematical defect was found. The earlier difference between axiom morphisms and axiom subobjects is not a manuscript flaw: Theorem 4.4 explicitly defines generation for an arbitrary morphism through its regular image. The proof needs initiality only for that image subobject.

(C) Minor issues

No necessary local correction was identified in this correctness pass. Equations and proof sketches below make implicit but valid categorical steps explicit; they are audit reconstructions, not proposed new hypotheses.

(D) Cross-section consistency failures

No confirmed consistency failure was identified. The functional outline was constructed before checking the proofs:

1. §2 fixes the ambient partial-map structures, equality of morphisms, restriction order, ranges, coproducts, completion, and the particular Turing-category definition. Its product-with-two example limits what a range functor may be assumed to preserve.
2. §3 obtains zero inverse images from a lifted switched conditional by one source Turing parameterization, then derives noncoverage and source inseparability. It depends on §2, not on internal deduction.
3. §4 first uses Appendix A to represent generated theorem and refutation domains. It applies §3 to interpreted theories and proves the independent inseparable-pair reduction criterion. The second half develops closure reflection, logical-translation Galois connections, change of ambient category, and the free signed first-order adjunction.
4. §5 uses the all-mono partial-inverse hypothesis to identify the splitting with a partial-map category. It constructs Turing slice categories, extension functors and their two adjunctions, then uses a global theorem point to transfer incompleteness between a theory and its constant family.
5. Appendix A supplies the prerequisite polynomial syntax/list algebras, Boolean operations, capture-aware substitution, finite-rule endofunctor, regular-image closure theorem, and first-order/propositional specializations. It assumes each required initial algebra; it does not claim that regularity and extensivity alone construct them.

## Dependency and typing checks

- In §3, the Turing property is used in the source category. No preservation of restriction products by the range functor is inferred. The noncoverage step alone uses the stated target join-preservation and nonzero-identity hypotheses.
- In §4, initial algebras are required for axiom subobjects. Theorem 4.4 sends an arbitrary axiom morphism to the generated theory of its image. Neither an algebra of separately labelled leaves nor its initiality is silently identified with that of the image.
- In §5, all monomorphisms in D must have partial inverses in C; this hypothesis is used for the slice restriction retract. The global theorem point is used only in Theorem 5.3 to obtain E_U B_U ≅ 1 and reflect the properties under discussion.
- Turing slice parameterization does not require a code independent of the base variable. For p:X→T, the parameter is ⟨p,a⟩:X→T×Q, where a:X→Q parameterizes the Q-component of the slice partial morphism. For an object T×X in R[T], a may depend on both coordinates. Fullness includes this total morphism.
- The unit of i*⊣Σ_i is correctly partial, with domain T×_U Y. It is not claimed total. Regular-image and inverse-image equalities are understood in the stated subobject orders; naturally isomorphic chosen representatives are not required to be literally equal.

## Every numbered proof and definition

Each entry lists its explicit assumptions and a reconstruction. “No confirmed defect” means the displayed argument has been reconstructed at ordinary mathematical proof level within the stated hypotheses; it does not assert a fresh kernel verification.

### Theorem 3.1 — `thm:comparison`
Anchor: printed p. 6; `sections/03-sections-and-inseparability.tex:17`.

Hypothesis use: Source Turing property and isomorphism b; target restriction, zeros, coproducts; F preserves restrictions, ranges, zeros and coproducts; disjoint P,N and bounds; lifted switched conditional; final nonzero and join-preservation hypotheses only for noncoverage.

1. Apply source parameterization to b⁻¹ℓπ₂:U×U⇀U and precompose with ⟨1_U,g⟩, obtaining hg=ℓg.
2. Apply F and its coproduct comparison to identify (Fg)*F(a₀)=(Fg)*N and (Fg)*F(a₁)=(Fg)*P.
3. The bounding inequalities force the latter two inverse images to coincide; their meet is the inverse image of PN=0, so both vanish.
4. If P∨N=1, totality and the explicitly assumed preservation of that join force 1_FU=0.

Status: no confirmed defect.

### Corollary 3.2 — `cor:separator`
Anchor: printed p. 7; `sections/03-sections-and-inseparability.tex:77`.

Hypothesis use: Exactly Theorem 3.1 hypotheses plus complementarity and total inverse-image preservation of binary joins.

1. The alleged s,ℓ satisfy the hypotheses of Theorem 3.1.
2. Its noncoverage conclusion contradicts P∨N=1.
3. No product preservation by F is used.

Status: no confirmed defect.

### Corollary 3.3 — `cor:source-conditionals`
Anchor: printed p. 7; `sections/03-sections-and-inseparability.tex:98`.

Hypothesis use: Theorem 3.1 data; total conditional for every complementary pair on U; target joins and nonzero identity.

1. The conditional branch equations give ε₀ℓ_c=i₀c′ and ε₁ℓ_c=i₁c after precomposition with c,c′.
2. The agreement law cancels their copairing because ran[c,c′]=c∨c′=1.
3. Restrictions then give exactly the switched inverse-image equations.
4. A hypothetical source separator is sent by F to a complementary target separator, contradicting Corollary 3.2.

Status: no confirmed defect.

### Proposition 3.4 — `prop:disjoint-joins`
Anchor: printed p. 7; `sections/03-sections-and-inseparability.tex:138`.

Hypothesis use: Restriction zeros, coproducts with total injections, existence of joins for parallel morphisms with disjoint restrictions.

1. The restrictions of i₁c and i₀c′ are c and c′.
2. Join upper-bound equations give the two prescribed branch values.
3. Both c,c′ lie below the restriction of the join, and c∨c′=1 forces totality.

Status: no confirmed defect.

### Proposition 4.1 — `prop:interpreted-theory`
Anchor: printed p. 9; `sections/03a-internal-theories.tex:93`.

Hypothesis use: Chosen-splitting extension of range functor; sentence-range splitting; for final assertion target Par(E,Mono) with E regular and validity factorization.

1. Functoriality carries both splitting equations; range preservation carries t_A=ran(c_A,S).
2. In Par(E,Mono), Lemma A.7 identifies the range with the regular image.
3. Factorization of the conclusion through v bounds the interpreted theorem domain by d_V.
4. Monotonicity of inverse image and meet transfers d_V∧(Fν)*d_V=0 to the interpreted domain.

Status: no confirmed defect.

### Theorem 4.2 — `thm:logical-comparison`
Anchor: printed p. 9; `sections/03a-internal-theories.tex:140`.

Hypothesis use: Theorem 3.1 data; split target; θ total; semantic consistency; both diagonal bounds and lifted switched conditional; total inverse images preserve binary joins; nonzero identity.

1. Pull back semantic consistency along F̂θ to get PN=0.
2. Theorem 3.1 supplies total g and zero inverse images of both pulled-back domains.
3. Compose inverse-image identities to obtain both asserted equalities for F̂(θg).
4. A complete interpreted theory would pull back to 1_FU=0; completeness in the source maps to completeness in the target, giving the second contradiction.

Status: no confirmed defect.

### Corollary 4.3 — `cor:domain-incompleteness`
Anchor: printed p. 10; `sections/03a-internal-theories.tex:202`.

Hypothesis use: Inseparable pair a,b; total θ and ν; t₀ bounds; total inverse images preserve joins; candidate extension t≥t₀ is consistent.

1. A complementary separator e,e′ of t,ν*t pulls back along θ to disjoint idempotents.
2. Totality and join preservation make those pullbacks complementary.
3. Monotonicity and the t₀ bounds make them a separator of a,b, impossible.
4. If t∨ν*t=1, the consistent pair itself is such a separator.

Status: no confirmed defect.

### Theorem 4.4 — `thm:first-order-reflection`
Anchor: printed p. 11; `sections/03b-internal-adjunctions.tex:27`.

Hypothesis use: Regularity; finite disjoint stable coproducts; initial syntax and derivation algebras for each relevant axiom subobject.

1. Leastness of the generated formula subobject gives extensivity and monotonicity.
2. C(A) contains j_!Gen(A), so C(Gen(A))≤C(A); restriction to sentences gives idempotence.
3. For closed T, Gen(A)≤T iff A≤T.
4. For arbitrary a:A→S, regular image factorization gives Hom_D/S(a,J(T)) either empty or singleton according as im(a)≤T; this is equivalent to Gen(im(a))≤T, naturally.
5. Only image subobjects need initial derivation algebras; the proof does not assume an initial algebra for the unquotiented axiom morphism a.

Status: no confirmed defect.

### Theorem 4.5 — `thm:translation-galois`
Anchor: printed p. 11; `sections/03b-internal-adjunctions.tex:95`.

Hypothesis use: Logical translation preserving syntax, admissible substitution and rule instances; generation hypotheses for both presentations.

1. Pulling C_Q(T) back along σ_Φ gives a P-rule-closed formula subobject containing σ_S*T.
2. Initiality/leastness bounds C_P(σ*T) by that pullback; restriction to sentences proves inverse-image closure.
3. The regular-image/pullback Galois correspondence and generation reflection yield σ_#⊣σ*.
4. Apply closure preservation to Gen_Q(σ_!A), then extensivity and idempotence, to obtain the generation identity.
5. Composition of images and pullbacks yields both composition identities; these are equalities of subobject classes.

Status: no confirmed defect.

### Proposition 4.6 — `prop:deduction-comparison`
Anchor: printed p. 12; `sections/03b-internal-adjunctions.tex:179`.

Hypothesis use: G regular; σ:GS₁→S₂ total; each specified p_A commutes with sentence conclusions; optional L⊣R for the final assertion.

1. The commuting p_A gives LGen₁(A)≤Gen₂L(A) after taking regular images.
2. Apply Gen₂ and combine this inequality with A≤Gen₁(A) to get Gen₂LGen₁=Gen₂L.
3. Regularity gives im K(a)=L(im a), proving the slice square.
4. The inclusion of each image in its closure is the natural comparison; uniqueness through monomorphisms proves naturality.
5. For closed B, LRB≤B and the displayed inequality give LGen₁(RB)≤B; adjunction and extensivity make RB closed and yield the restricted adjunction.

Status: no confirmed defect.

### Theorem 4.7 — `thm:free-first-order-adjunction`
Anchor: printed p. 14; `sections/03b-internal-adjunctions.tex:295`.

Hypothesis use: All monos have partial inverses; decidable variable object; free nullary-predicate syntax and derivation constructions for every coefficient object X; consistency conditions defining the two categories.

1. A pair morphism f:X→S_P uniquely interprets the nullary predicates by closed sentences and variables identically.
2. Syntax initiality and induction preserve free variables, admissibility, substitution, and logical rules; the pair bounds put the generated axioms into T.
3. Restricting a logical translation to θ_X recovers f, giving inverse hom-set assignments.
4. Uniqueness gives naturality, functor laws, the displayed unit and counit.
5. For J_FO to land in Pair_c, interpretation of each sentence-indexed predicate as that sentence pulls a consistent closed theory back to one containing both signed axiom families.

Status: no confirmed defect.

### Corollary 4.8 — `cor:signed-first-order-incompleteness`
Anchor: printed p. 14; `sections/03b-internal-adjunctions.tex:334`.

Hypothesis use: Free-theory hypotheses; disjoint pair; generated free signed theory consistent.

1. The atomic inclusion reduces the pair to the theorem and refutation subobjects, so Corollary 4.3 proves the forward implication from inseparability.
2. A complementary separator gives a total Boolean map d:X→2 by the extensive coproduct decomposition.
3. Assign equality true, nullary predicates d, quantification the projection, and logical operations their Boolean truth functions.
4. Structural induction makes valuation invariant under admissible substitution; every logical axiom and rule preserves truth.
5. The true fiber is therefore a consistent complete extension, contradicting essential incompleteness when the pair is separable.

Status: no confirmed defect.

### Lemma 5.1 — `lem:partial-slice-turing`
Anchor: printed p. 15; `sections/04-theory-extensions.tex:32`.

Hypothesis use: R recursion category; C=Split(R); D=Tot(C) regular extensive; every D-mono has partial inverse in C.

1. D’s terminal object is restriction terminal in C by splitting the domain of each partial map; binary restriction products are inherited.
2. For X=(X₀,e), extend f:X×Q⇀Q to its underlying R-morphism X₀×Q⇀Q, parameterize by total a₀:X₀→Q, and restrict to a₀e, total on X.
3. For p:X→T, the total mono ⟨p,m_X⟩:X↪T×Q has a partial inverse over T.
4. A partial slice computation p×_TQ_T→Q_T has Q-component f:X×Q⇀Q; its total code a:X→Q gives parameter ⟨p,a⟩:p→Q_T and evaluation 1_T×τ.
5. For source T×X with X∈R the parameter may depend on both t and x; full R[T] contains it. Its objects are isomorphic, product-closed and prodominical; every partial-slice object is a restriction retract of Q_T, giving the split-completion equivalence.

Status: no confirmed defect.

### Theorem 5.2 — `thm:theory-extension`
Anchor: printed p. 15; `sections/04-theory-extensions.tex:89`.

Hypothesis use: Monic theory inclusion i:T↪U; partial-map slice categories; pullbacks; preceding Turing setup only for their identification with split recursion categories.

1. Monicity of i makes a span between postcomposed objects commute over U iff it commutes over T, proving full faithfulness.
2. A span from Σ_i p to q factors its right leg through the pullback, giving Σ_i⊣i*.
3. A span from q to Σ_i p factors its monic left leg through the same pullback, giving i*⊣Σ_i; its unit has exactly that partial domain.
4. The assignments commute with pullback composition, hence are natural.
5. An isomorphism from 1_U to an image object would make i split epic and thus invertible; the square and composition law follow from ui=t.

Status: no confirmed defect.

### Theorem 5.3 — `thm:associated-incompleteness`
Anchor: printed p. 17; `sections/04-theory-extensions.tex:190`.

Hypothesis use: Regular extensive D; partial-map identification; parameterized syntax/derivation construction in every slice; global λ:1→S factors through each relevant theory; u consistent.

1. B_U=U×− and E_U=λ_U* preserve finite limits, regular images and finite coproducts in the displayed source and target slice categories.
2. Applying these functors to a closed formula subobject gives a rule algebra containing the transported axioms; initiality implies the transported sentence theory is closed.
3. They preserve consistency/completeness, while E_UB_U≅1, so consistent complete extensions transfer both ways.
4. The same retraction reflects totality and transfers total extensions of δ_u; total Boolean extensions correspond exactly to complementary separators.
5. Corollary 4.3 supplies inseparability for each consistent extension of a base theory admitting the given reduction.

Status: no confirmed defect.

### Definition A.1 — `def:categorical-syntax`
Anchor: printed p. 68; `appendices/a-syntax-and-theories.tex:188`.

Hypothesis use: Parameterized initial K-algebra; parameterized list algebra; decidable equality on V.

1. This is a definition, not an existence assertion.
2. The preceding polynomial expressions explicitly type K on objects and morphisms.
3. Lambek initiality supplies the constructor decomposition, and parameterization gives the stated induction and folds.

Status: definition checked.

### Definition A.2 — `def:sentence-object`
Anchor: printed p. 69; `appendices/a-syntax-and-theories.tex:261`.

Hypothesis use: Formula free-variable map and list nil.

1. This is a pullback definition of the subobject of formulas with empty free-variable list.
2. Nil:1→W is monic; pullback therefore gives a monic sentence inclusion.
3. The displayed free-variable equation for negation gives its total restriction ν:S→S.

Status: definition checked.

### Proposition A.3 — `prop:categorical-substitution`
Anchor: printed p. 70; `appendices/a-syntax-and-theories.tex:327`.

Hypothesis use: Parameterized K-initiality; total Boolean equality on V; extensive products/coproducts; defined algebra retaining original expressions and recursive values.

1. The specified K_E-algebra has carriers E×(Tm×Tm) and E×(Fm×(1+Fm)).
2. Its unique fold projects to the identity on the original syntax by initiality.
3. Its other components are the required total term-substitution and formula-result morphisms.
4. Pulling back the successful coproduct injection defines Adm and a_F; extensivity gives the complement of its inclusion.

Status: no confirmed defect.

### Definition A.4 — `def:deductively-closed`
Anchor: printed p. 71; `appendices/a-syntax-and-theories.tex:438`.

Hypothesis use: Finite-rule endofunctor H in D/F and monic m:T↪F.

1. This defines closure as an H-algebra over the formula object.
2. Monicity makes its structure unique when it exists.
3. For an inclusion of closed subobjects, composition with the target mono identifies the two algebra-morphism composites.

Status: definition checked.

### Theorem A.5 — `thm:least-theorem-subobject`
Anchor: printed p. 72; `appendices/a-syntax-and-theories.tex:457`.

Hypothesis use: Regular D; finite coproducts; finite rule arities; initial H-algebra.

1. Factor the conclusion c=me with e regular epic.
2. Finite products, pullback and coproduct of coequalizers show H(e) regular epic.
3. The commuting square against m makes eδ coequalize the kernel pair of H(e); descend to the unique rule algebra on the image.
4. For every closed subobject U, initiality provides a map P→U over F; the image universal property gives T→U.
5. Thus the image is closed and least.

Status: no confirmed defect.

### Theorem A.6 — `thm:first-order-theory`
Anchor: printed p. 73; `appendices/a-syntax-and-theories.tex:553`.

Hypothesis use: Syntax and admissible substitution; the seven explicitly typed schemes; H_A initial for axiom mono A↪S.

1. The rule family is the preceding finite-rule construction with arities 0,1,2.
2. Theorem A.5 supplies the least closed formula image.
3. Regular-image stability under pullback along S↪Fm gives exactly the sentence image equality.

Status: no confirmed defect.

### Lemma A.7 — `lem:range-regular-image`
Anchor: printed p. 73; `appendices/a-syntax-and-theories.tex:584`.

Hypothesis use: S has ranges and all restriction idempotents split; D=Tot(S) regular; image mono m has partial inverse r.

1. mr receives f=me.
2. Split any receiving restriction idempotent a=js; sf is total because j is total and jsf=f.
3. Since j is a total mono receiving f, the regular image factors as m=ju.
4. Then am=m and a(mr)=mr, proving mr is the least receiving restriction idempotent.

Status: no confirmed defect.

## Central unnumbered arguments

- **§2, pp.4–6, definitions and unnumbered examples.** Restriction splitting, all-idempotent Karoubi formula, partial-map spans, range-join formula, non-product-preserving range functor. The span construction is typed over its endpoints and composes by pullback. Range of a copairing is least receiving both idempotents. The product-with-{0,1} example preserves restriction domains and images, while the comparison misses mixed second coordinates. No cited-author attribution was independently authenticated.

- **§3, p.6, summand restriction idempotents.** ε₀ε₁=0 and ε₀∨ε₁=1. Precomposition with each total coproduct injection proves zero meet; any common receiving upper bound fixes each injection, hence their copairing identity.

- **§4, pp.8–9, chosen-splitting extension before Proposition 4.1.** F̂ is a range functor. Insert m_e r_e=F(e) and source support equations to prove composition and identity. The displayed restriction formula makes it a restriction functor. Conjugate a receiving idempotent through m_d,r_d for leastness of the range. The explicit κ and inverse prove coproduct preservation.

- **§4, p.10, after Corollary 4.3.** An inseparable pair on an original object remains inseparable in Split(R). The endomorphism set of (U,1_U), restriction operation and order coincide with those of U; an alleged new separator would already be an original separator.

- **§4, p.12, unnumbered varying-presentation reflection.** Ax_V(D)→Th_V(D) is left adjoint to inclusion. Theorem 4.5 gives σ_!Gen_P(A)≤T iff σ_!A≤T for closed T. The hom correspondence leaves the translation unchanged, so composition and naturality are immediate.

- **§4, p.13, after Proposition 4.6.** Adjoint transpose constructs deduction comparison p_A. The displayed mate gives H_A R_Φ(P′)→R_Φ(P′); source initiality supplies P_A→R_Φ(P′). Transposition gives K_ΦP_A→P′, and regular G plus the sentence square restrict it to the stated sentence carriers.

- **§5, p.15, C≃Par(D,Mono).** All-mono partial inverses identify C with the partial-map category. Represent a span by f m†. Splitting a restriction yields its inverse construction. The universal property of the pullback identifies composition; partial inverses of total monos are unique.

- **§5, p.16, after Theorem 5.2.** Σ_i preserves binary restriction products but generally not terminal object. Products of image objects over U equal their products over T because i is mono. The terminal image is i:T→U; when i is proper this is not terminal.

- **§5, p.17, after Theorem 5.3.** Infinite c.e. carriers are computably isomorphic to N. Duplicate-free enumeration is total on every index for an infinite c.e. set; inverse search terminates on each element of that carrier. This supports the statement only for extensional partial computable maps and infinite c.e. carriers, the scope stated.

- **Appendix A, pp.67–69, Boolean object/list/free-variable constructions.** Boolean truth functions, conditionals, membership/deletion and free-variable folds. Extensivity decomposes finite Boolean powers into jointly epic summands; listed truth tables satisfy the Boolean identities. Parameterized list folds define the three recursions. Initial K-folds define free-variable lists, retaining repetitions.

- **Appendix A, pp.70–71, admissibility equation and identity/absent-variable substitutions.** Capture restriction, identity substitution and absence invariance. Boolean decomposition at binder equality yields the displayed disjoint-domain equation. Simultaneous structural induction handles the term/formula equations. In the unequal binder case, deletion transports the absence condition into the body; the Boolean C branch then succeeds.

- **Appendix A, p.73, after Theorem A.6.** Generated sentence subobjects are closed, least, and monotone. C(A) contains Gen(A), so leastness gives C(Gen(A))≤C(A); pullback and extensivity give closure. If U is closed and contains A, leastness C(A)≤C(U) pulls back to Gen(A)≤U.

- **Appendix A, p.74, propositional specialization.** The finite-rule theorem constructs propositional generated theories. Take the explicitly typed nullary logical/axiom family, no unary rule and the modus-ponens binary family. Theorem A.5 applies conditionally on its initial algebra; the signed axioms are introduced through their image subobject.

(E) Acceptance conditions, non-negotiable

No mathematical repair condition arises from this assigned-scope audit. Before using a stronger implementation theorem as evidence for Theorem 4.4, its hypotheses must still be specialized to initiality for axiom subobjects; the manuscript proof above already has the required scope. This is a formalization correspondence condition, not a reason to change the theorem.

(F) Not checked / uncertainty log

- No fresh Lean build, intended-statement check or transitive axiom audit was executed by this reviewer. The report does not upgrade any open formalization row.
- The applications in §§6–10 and Appendices B–D are outside this assigned scope, except that their names and dependencies appear in the supplied inventory.
- Primary-source theorem-number attributions to Heller, Cockett–Lack, Cockett–Hofstra and others were not independently authenticated here. The core arguments above were checked directly.
- The Knuth–Larrabee–Roberts text was consulted in Section 1 and substantial passages through Section 16, including §§4–5 on definition placement and §§15–16 on referee criticism. This reviewer did not read the full manual and makes no claim of complete manual compliance. The separate writing reviewer has the full-manual assignment.
- The manual OCR has gaps and distorted mathematical typography. None is used as mathematical evidence for the manuscript’s results.

Strongest confirmed blocker: none in the assigned scope. Strongest suspected but unconfirmed blocker: none retained after checking Lemma 5.1 and Theorem 5.3. Most important unchecked item: whether the concrete applications satisfy all general hypotheses, together with exact Lean/manuscript correspondence. The scoped conclusion does not rely on missing source material; a whole-paper recommendation does. Final recommendation: **unknown** for the whole paper; no rejection condition was established by this core mathematical audit.
