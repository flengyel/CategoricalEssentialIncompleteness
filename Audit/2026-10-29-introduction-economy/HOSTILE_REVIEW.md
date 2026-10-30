# (A) Kill-shots / hard blockers

None confirmed in the reviewed revision.

This is an author-side hostile audit under HostileRefereeGPT — Cat/Rec, not external peer review. The reviewed source is `manuscript/essential_incompleteness_via_local_connectedness_v2.tex`, SHA-256 `cae09d2ed4cb0d9606eb7973ddfb4143fcd4736e7ccc3e0e8dd6c177248993b1`. The comparison source is `build/introduction-economy/before.tex`.

The present pass checks every section for mathematical antecedents, types and the scope of its assertions; it checks the complete revision diff. The general range-functor theorem and its coproduct comparisons received a fresh calculation. Sections 1–7 and Appendix B also received separate author-side checks. Unchanged substantive constructions retain the proof audit in `Audit/2026-10-29-self-contained-local-connectedness/HOSTILE_REVIEW.md`; this report does not present the repetition as new external review or formal verification.

The initially shortened Introduction omitted the c.e. restriction from the asserted failure of composition for the primed systems. That was a confirmed scope defect: for T equal to true arithmetic, the pointwise relation is extensional program equality and composition is valid. The current Introduction and Section 3 explicitly restrict the cited obstruction to consistent c.e. extensions of PA. The pointwise relation is now described in Section 3. This defect is resolved in the reviewed hash, rather than silently downgraded.

# (B) Major weaknesses

None confirmed. The following are the central checks of the revision.

| Anchor | Claim, typed calculation and status |
|---|---|
| Section 2, definition of a range functor | The covariant functor preserves restrictions, ranges, zeros and binary restriction coproducts. The comparison is explicitly χ_(X,Y):FX+FY → F(X+Y), with χ=[Fi₀,Fi₁]. The equation F[f,g]χ=[Ff,Fg] is correctly typed. Products are not included in the definition. |
| Section 2, product-preservation counterexample | For F:Pfn→Pfn, F(X)=X×{0,1} and F(f)=f×1, identity and composition are preserved. Domain and image partial identities, empty maps, and tagged coproducts are preserved. The product comparison sends ((x,y),a) to ((x,a),(y,a)); when X and Y are nonempty it misses pairs with unequal last coordinates. Thus range functors need not preserve restriction products. Evidence: explicit example and direct calculation. |
| Theorem `thm:local-lifting`, hypotheses | The source is an isotypical prodominical recursion category with ranges and binary restriction coproducts. The target is split and locally connected, with ranges, zeros, coproducts, weak choice and inverse images preserving binary joins. The target is not required to have products. Lifting is required for each complementary source pair, not for every target pair. The stated nonzero-image condition remains present. |
| Theorem `thm:local-lifting`, source calculation | With ℓ:U⇀U+U and u=b⁻¹ℓ, universality in the source supplies total g:U→U with τ(g×1)=uπ₂. Precomposition with ⟨1,g⟩ gives τΔg=ug and hence bτΔg=ℓg. All products, the pairing and Δ occur in the source category. |
| Theorem `thm:local-lifting`, target calculation | The lift equation is Fℓ=χs. Consequently H=χ⁻¹F(bτΔ):FU⇀FU+FU and E=Fg:FU→FU satisfy HE=sE. This uses composition and the coproduct comparison only. The proof never identifies F(U×U) with FU×FU, never replaces FΔ by Δ, and never claims Fτ is a target Turing morphism. |
| Theorem `thm:local-lifting`, contradiction | Preservation of restrictions and coproduct summand domains gives E*F(a₀)=E*Γ′ and E*F(a₁)=E*Γ. The separator inequalities give both reverse inclusions between E*Γ and E*Γ′. They are equal and complementary, because E is total and target inverse images preserve joins. Thus 1_FU=0. No reflection of totality or zero is inserted. |
| Proposition `prop:disjoint-joins` | The source join has restriction above both complementary domains and is total. Its two branch equations are transported using χ⁻¹Fℓ. This arrow and the unique target section agree after [Γ,Γ′], whose range is the identity; range agreement proves equality. Neither preservation of source arrow joins nor product preservation by F is used. |
| Lemma `lem:switch` and Corollary `cor:pair` | The explicit χ orientation agrees with the theorem. The dovetailing program is T-provably total from the proved complementary predicates, with the displayed exact graph. Its interpretation is the target section in every model. The extension statement now explicitly assumes T′ is consistent. |
| Propositions `prop:model`, Theorem `thm:faithful`, and the theory-extension square | These particular model functors do preserve products by their object definitions and the PA-provable product graph equations. This is additional structure of these functors, not a consequence of being range functors. The quotient functors preserve the listed operations because the same program representatives and defining proofs are retained under theory extension. |
| Section 8, categories and arrows | C_rec has c.e. numerical carriers and functions computed by partial recursive programs defined on every element of the stated source. No ambient-total extension is assumed. E=C_rec^J is the total category of covariant diagrams and natural transformations. A=Par(E,Mono) is its split partial-map category. R_X is the specified full isotypical subcategory; it is R_X, rather than E or all of A, that is asserted and proved to be a recursion category. |
| Section 8 and Proposition `prop:fork-cosheaves` | The underlying Set diagram determines a Set-valued cosheaf, with global value given by its pushout. No C_rec-valued global quotient or recursive presentation of that quotient as an ordinary carrier is asserted. Products and selected domains remain those of the diagram category. The global-value examples correctly distinguish these operations from pointwise products or subsets on every open. |
| Theorem `thm:fork-turing` and Proposition `prop:fork-recursion` | Replacing “total recursive value maps” by arrows of C_rec preserves the intended source-total condition. The numerical programs first test membership in the specified c.e. domains. Specialization reproduces those exact domains. The central output filter ensures naturality, and both directions of the central domain equality remain proved. Fullness retains the total parameters in R_X, while the displayed splitting functor is fully faithful and essentially surjective. |
| Proposition `prop:endpoint` and Theorem `thm:cosheaf-observation` | E_j:A→K is defined on representing spans and preserves the indicated componentwise structures. The chosen Turing morphism remains universal at endpoints 1 and 2; the central counterexample precludes an unwarranted claim about E₀. Φ_i:A→Pfn uses total probes and is separately given numerical names. The observation sets are preimages along the total atom map from N², so their enumeration and the completeness contradiction do not assume a general syntax carrier is decidable. |
| Appendix B, Proposition `prop:fork-syntax-initial` | P acts on E, the total diagram category. A total algebra gives a finite recursive fold total on the syntax carriers. Naturality and uniqueness follow by tree induction. The revision does not extend this initiality assertion to arbitrary partial algebras. |
| Appendix B, Theorem `thm:fork-proof-presentation` | Proof carriers are c.e. via finite collections of c.e. axiom-leaf tests. Natural transitions preserve validity even when labels are identified. Component conclusion images give the least rule-closed domain. The one-node proof maps give the atomic inequalities. The valuation uses positive leaves of both proposed proofs; disjointness makes every negative leaf true. The componentwise contradiction proves the internal zero-domain equation without natural valuations or global separators. |
| Appendix C, Proposition `prop:missing-lift` | The source still consists of K-c.e. domains with ordinary partial recursive value extensions. Ordinary specialization of the program and oracle-domain indices yields the total Turing parameters. The faithful inclusion preserves even products, but the required total section is nonrecursive and cannot lift. The appendix continues to refute only the statement with lifting omitted. |

All entries above have derivation or structural-argument evidence. None rests merely on a successful build.

# (C) Minor issues

No unresolved consequential antecedent or notation defect was found in the reviewed source. The reported local repairs are present:

- The lift in `thm:local-lifting` is introduced as the total section, restoring the missing grammatical predicate.
- The nonnumericality paragraph explicitly names R_X as the subject of the terminal-subobject calculation.
- The global-product example no longer applies H, a J-diagram, to the open X without naming its associated cosheaf.
- The inverse-image carrier formula in `prop:fork-structure` uses the domain subdiagram D_e rather than treating the restriction idempotent e_j as a set.
- Appendix C names the total arrows of C_K explicitly, rather than using “their” with partial functions as its nearest antecedent.
- The word-object universal property names its semigroup and source map; the numerical splitting comparison states the functor's source, target and action.
- The switching proof distinguishes the chosen program index e_s, its graph G_(e_s), and the quotient arrow s=[e_s]_T. The weak-choice argument identifies D_p as a domain subdiagram, rather than an idempotent.

The phrases “computable diagram”, “computational diagram”, and “computational cosheaf” have been removed. The replacements supply the objects, arrows, equality and naturality equations rather than renaming E as a recursion category. “Theory extending t₀” is explicitly a domain of S in A containing t₀ and closed under the stated logical rules.

# (D) Cross-section consistency failures

None confirmed in the reviewed hash.

1. **Product preservation has the correct scope.** The general theorem needs no such property. The concrete model and endpoint functors have it by separate proofs. The new counterexample prevents the two assertions from being conflated.
2. **Internal inseparability and effective incompleteness remain distinct.** The faithful model interpretation supplies internal inseparability for every consistent extension, without a c.e. assumption. The arithmetic incompleteness conclusion adds c.e. proof enumeration and the finite-computation inclusions. True arithmetic remains the explicit counterexample to deducing logical incompleteness from internal inseparability alone.
3. **The categorical construction remains nonnumerical.** R_X and its Turing morphism are constructed. Syntax and proofs lie in its restriction splitting A. Endpoint functors provide observations of this source; they do not replace it by the classical category.
4. **The two three-point pairs remain distinct.** Full inclusion verifies the range-functor theorem. The singleton-output pair used in the propositionally presented theory is checked by endpoint universality. The text does not identify it with the theorem's summand-output pair without a proof.
5. **Domains and carriers remain distinct.** Theorems and consistency are stated using restriction idempotents. Split subdiagrams and observed carriers are introduced separately. Logical negation is a constructor; its inverse-image operation is the monotone domain operation used in the formulas.
6. **The extension class is unchanged.** Every extension in the three-point theorem is a rule-closed domain in A containing t₀; its components are therefore c.e. The theorem does not quantify over arbitrary subobjects of an enlarged category or all externally specified theories.
7. **Attribution and conditional scope survive the shorter Introduction.** The original Lengyel 2004 statement is still paired with its corrections and is not said to require product preservation. The valid uniform quotients remain separated from the invalid primed proposal under its c.e. hypothesis. No claim that this proves all of the Di Paola–Heller program or strictly generalizes Bernardi's theorem is introduced.

# (E) Acceptance conditions, non-negotiable

These conditions are satisfied by the reviewed revision and must survive later edits.

1. **Preserve the comparison types.** Deliverable: the range-functor definition and `thm:local-lifting`. Endpoint: χ has direction FX+FY→F(X+Y), Fℓ=χs, and H=χ⁻¹F(bτΔ). A product identification substituted for functoriality would require a new hypothesis and invalidate the currently stated generality.
2. **Retain the lifting hypothesis.** Deliverable: `thm:local-lifting`, `prop:disjoint-joins`, Appendix C. Endpoint: the theorem retains the specified lifts, the proposition proves a sufficient condition, and the example concerns only omission of lifting. Failure would require dropping the general inseparability conclusion.
3. **Retain the actual recursion category and arrow classes.** Deliverable: Section 8 and Appendix A. Endpoint: C_rec maps are total only on declared carriers; E, A and R_X are distinguished; exact-domain Turing universality and the splitting equivalence remain proved. Removing these would reopen the nonnumerical construction.
4. **Preserve effective observation and the defined extension class.** Deliverable: `cor:arithmetic` and `thm:cosheaf-observation`. Endpoint: c.e. proof enumeration or c.e. endpoint observations, the total atom reductions, and consistency are explicit. Internal domain inseparability alone is not a substitute; without this bridge the essential-incompleteness claim must be dropped.
5. **Retain the finite consistency calculation.** Deliverable: `thm:fork-proof-presentation`. Endpoint: both proofs contribute their positive leaves, all negative leaves are verified, and the componentwise contradiction is converted to the stated zero-domain equation. Replacing this with an assumed global separator would not establish the construction.
6. **Keep the c.e. scope of the primed-system obstruction.** Deliverable: Introduction and Section 3. Endpoint: the failure-of-composition claim remains restricted to the theories covered by the cited result. Omitting that restriction reintroduces the exhibited true-arithmetic counterexample.

# (F) Not checked / uncertainty log

- This is an author-side review of the revision, with prior mathematical audits reused for unchanged arguments. It is not external peer review and does not certify publication value or novelty.
- The current pass does not repeat the prior inspection of every published source scan. Historical statements were compared with the existing source-check record and were checked for altered scope in this revision.
- The fixed PA-verifiable programming system, acceptable numberings, finite recursive encodings, first-order completeness and downward Löwenheim–Skolem remain standard or explicitly stipulated background. No new implementation-level arithmetization was verified.
- No theorem here is claimed to have been formalized in Lean. The older Lean axiom count is irrelevant to the new constructions.
- Compilation and rendering are separate verification work; this report does not infer proof correctness from them.

Strongest confirmed blocker: none unresolved. Strongest suspected but unconfirmed blocker: none identified. Most important unrepeated input: the fixed PA programming system's graph specifications and the previously checked published-source attributions. The mathematical audit does not depend on unavailable private construction proofs; those constructions remain included. Final recommendation: **unknown as a publication decision; no confirmed mathematical defect in the reviewed revision**.
