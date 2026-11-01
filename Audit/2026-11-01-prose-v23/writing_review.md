# Mathematical-writing review of §§6–7, version 22

The main difficulty is compression at changes of mathematical level: from an isomorphism of subobjects to provable equivalence of predicates, from a decomposition of slice categories to a decomposition of algebra categories, and from a comparison theorem to the particular inverse-image equations needed in the application. These passages can be made explicit without repeating Appendix A. Most of the terminology is established category theory or recursion theory; the local phrases “literal specializations” and “sentence-conclusion pullback” can be replaced by the actual operations they denote.

Reviewed manuscript: *Logical consequence and essential incompleteness in recursion categories*, version 22. Primary scope is §§6–7, including the new soundness and uniform-family material. Source paths below are relative to `output/manuscript/local_connectedness/`. Line numbers and printed page numbers refer to the unedited version 22.

The governing source consulted is Knuth, Larrabee, and Roberts, *Mathematical Writing*, Stanford course report, supplied text `tmp/review_sources/klr.txt`, §1, printed pp. 1–6. In particular: point 5 recommends usually self-contained theorem statements; points 10–11 require connected exposition and definitions at first introduction while allowing complementary explanations; point 14 calls for consistent notation; point 17 concerns left-to-right readability; point 26 warns against strings of nouns used adjectivally and unnecessary jargon. The categorical typing requirements below are the skill's supplementary convention and this reviewer's application of those principles, not a purported verbatim rule from the report.

## Current outline and dependencies

| Location | Function and principal result | Dependencies |
|---|---|---|
| §6 opening | Defines the interpretation of object terms and program graphs; Proposition 6.1 proves functoriality and preservation. | Arithmetized graph identities of §5. |
| §6.1 | Constructs complementary conditionals in the syntactic category; Lemma 6.2 and Corollary 6.3 apply the lifting criterion. | Σ₁ search, range interpretation, Theorem 3.5. |
| §6.2 | Restricts the interpreted splitting to total maps; Proposition 6.4 proves preservation of finite limits, coproducts, and regular images. | Predicate presentation and equivalence of Lemma 5.3. |
| §6.3 | Separates interpretation of codes in the standard arithmetic model from satisfaction in a model of the axioms. Lemma 6.5 proves semantic substitution; Proposition 6.6 proves soundness by induction on standard finite derivations. | Realization of free variables and substitution; actual derivation carriers from §5; logical schemes of Appendix A. |
| §6.4 | Defines the ultrapower functor, proves preservation properties and its natural comparison with arithmetic interpretation, and transports soundness. Lemmas 6.7–6.8 and Theorem 6.9. | Choice, Łoś's theorem, Proposition 6.6, and the predicate-category equivalence. |
| §7.1 | Defines the theorem predicates and diagonal domains; Lemmas 7.1–7.2 supply the reduction and proof-search map. Theorem 7.3 and Corollary 7.4 give incompleteness and recursive inseparability. | §§3–6; first-order completeness. |
| §7.2 | Forms one parameterized axiom and derivation family. Proposition 7.5 identifies its numeral fibers; Theorem 7.6 constructs a uniform independent-sentence morphism. | General derivation realization of Lemma 5.8; regular-image result of Appendix A; finite extensivity; prior soundness and arithmetic reductions. |
| §7.3 | Constructs the numerical category and realizes syntax and derivations in its total splitting; Proposition 7.7. Applies the comparison results to the numerical theory objects. | Recursive tree evaluation and the categorical construction of Appendix A. |
| §7.4 | Records functoriality of numeral instances under theory extension and compares the numerical argument with Bernardi. | §7.3, earlier inseparability, and the cited example of a precomplete equivalence relation. |

The central purpose of the reviewed material is to interpret internally constructed consequence objects, establish their semantic disjointness from refutation, and apply the diagonal comparison both to individual arithmetic presentations and to a uniform family of them. The current order supports those dependencies. No reorganization is needed.

## Findings and recommended repairs

| Priority and anchor | Difficulty | Basis | Repair |
|---|---|---|---|
| Necessary clarification: §7.1, Theorem 7.3 proof, p. 30; `08-essential-incompleteness-of-arithmetic.tex` 219–221 | “a total g whose two inverse images vanish” does not name the map along which inverse images are taken or the two subobjects. | KLR §1 points 10 and 17; explicit typing. | Name `g:ω→ω` in `S_PA`, put `γ=F_N(g)`, and display the inverse images of `Th_Γ` and `Ref_Γ` along `(G_N θ)γ` as empty. |
| Necessary clarification: §7.2, Proposition 7.5 proof, p. 32; `08a-uniform-theories.tex` 107–133 | The inference endofunctors' domains are left implicit; “an equivalence of algebra categories with” prints only the target category. | KLR §1 points 11 and 14; explicit category and functor types. | Give the endofunctor types and the full equivalence `Alg(H_E) ≃ Alg(H_{A_{Γ_e}}) × Alg(H_{≠e})`. Preserve the existing pullback argument and initiality argument. |
| Necessary clarification: §7.2, p. 33; `08a-uniform-theories.tex` 157–160 | “identifies Prov(ē,z) with the theorem predicate” conceals whether equality means extensional truth, provable equivalence, or equality of chosen formulas. | KLR §1 points 14 and 17; object/presentation distinction. | State that equality of the represented subobjects gives `PA ⊢ ∀z(Prov(ē,z) ↔ Prov_{Γ_e}(z))`. Both predicates imply `Sent(z)`, so the equivalence over the sentence subobject extends to all numerical inputs. |
| Necessary clarification: §6.4, p. 28; `06-interpretation-in-models.tex` 497–509 | “For a sentence-code representative s=[s_i]∈G_M S” calls an equivalence class a representative and does not state that every coordinate is a standard sentence code, as required to define every `φ_{s_i}`. | KLR §1 points 11 and 17; representatives versus classes. | Write: “Let `(s_i)_{i∈I}∈(G_N S)^I`, and put `s=η_S([s_i])∈G_M S`.” Then state the membership formula. This also makes the chosen comparison with `G_M S` explicit. |
| Local terminology: §7.2, p. 31; `08a-uniform-theories.tex` 19–21 | “use the literal specializations” names a syntactic operation by an unnecessary adjective and weak verb. | KLR §1 point 26. | “For each `e∈N`, define `A_{Γ_e}↪S` by the predicate `Ax(ē,z)`.” Preserve this specific choice of formula, which matters to the fiber calculation. |
| Local terminology: §7.1, p. 28; `08-essential-incompleteness-of-arithmetic.tex` 27–28 | “sentence-conclusion pullback” compresses the base-change operation into a noun compound. | KLR §1 point 26. | “Thus `P_Γ` is obtained by pulling back the full conclusion morphism along `S↪Fm`.” |
| Local typing: §7.1, Theorem 7.3, p. 30; `08-essential-incompleteness-of-arithmetic.tex` 189–192 | “total source morphism” uses a relative category designation inside a theorem statement. | KLR §1 point 5. | “there is a total morphism `g:ω→ω` in `S_PA` ...” |
| Optional exposition: §7.2 opening, p. 31; `08a-uniform-theories.tex` 4–27 | The construction starts with notation before explaining why another derivation object is needed. | KLR §1 points 12–13. | Add one concrete opening sentence: “We construct one derivation object for all computably enumerable axiom presentations extending PA.” The remaining paragraph supplies the precise meaning. |
| Optional economy: §6.4 ending, p. 28; `06-interpretation-in-models.tex` 511–517 | The last paragraph repeats the representative-replacement argument of Lemma 6.8. Its substantive point, that soundness applies to the full interpreted proof carrier, is worth retaining. | Skill economy rule, with KLR §1 point 11's allowance for useful complementary explanations. | State this point directly using `η_{P_{A,S}}`; cite Lemma 6.8 rather than reproduce the replacement argument. Do not remove the domain of the soundness assertion. |

## Exact replacements for the principal clarifications

For the end of Theorem 7.3's proof:

```latex
For $M=\N$, the theorem supplies a total morphism
$g:\omega\to\omega$ in $S_{\PA}$. Put
$\gamma=F_{\N}(g)$. Its conclusion is
\[
 ((G_{\N}\theta)\gamma)^{-1}(\mathsf{Th}_\Gamma)
 =((G_{\N}\theta)\gamma)^{-1}(\mathsf{Ref}_\Gamma)
 =\varnothing.
\]
Thus neither $\Theta(\gamma(n))$ nor its negation code is a
theorem code, for every $n\in\N$.
```

For the inference endofunctors in Proposition 7.5:

```latex
Let
\[
 H_E:\mathcal B/(E\times\Fm)\longrightarrow
        \mathcal B/(E\times\Fm)
\]
be the inference endofunctor for the family rules. Restricting
these rules to $E_{\ne e}$ defines an endofunctor
\[
 H_{\ne e}:\mathcal B/(E_{\ne e}\times\Fm)\longrightarrow
        \mathcal B/(E_{\ne e}\times\Fm).
\]
```

After the proof of the natural isomorphism, print the full equivalence:

```latex
The equivalence $\Xi_e$ and this natural isomorphism induce
\[
 \operatorname{Alg}(H_E)\simeq
 \operatorname{Alg}(H_{A_{\Gamma_e}})\times
 \operatorname{Alg}(H_{\ne e}).
\]
```

For the theorem predicates:

```latex
Proposition~\ref{prop:arithmetic-theory-fibers} identifies the
subobjects represented by $\operatorname{Prov}(\bar e,z)$ and
$\operatorname{Prov}_{\Gamma_e}(z)$. In the predicate
presentation, this means
\[
 \PA\vdash\forall z\,
 \bigl(\operatorname{Prov}(\bar e,z)
       \leftrightarrow\operatorname{Prov}_{\Gamma_e}(z)\bigr).
\]
```

## Definition and notation audit

- `B_T`, `P_T`, and `J_T` are defined and distinguished. The use of an equivalence rather than an equality of categories is correct in §6.2 and in Lemma 6.8.
- `V_K`, `v_K`, `e_K`, and their ultrapower analogues have explicit set-theoretic types. The distinction between `N` interpreting codes and `K` interpreting formulas is mathematical and should remain.
- `Fm`, `Adm`, free variables, sentence inclusion, and the inference endofunctor are supplied by Appendix A and the realization in §5. They should be cited, not redeveloped in §6 or §7.
- “Sentence theory” is defined in Appendix A. “Regular image,” “finite extensivity,” “fiber,” “slice category,” “initial algebra,” “parameterized Turing property,” and “partial inverse” are established terms in their stated settings. They are not examples of invented jargon.
- The numeral-fiber proof uses the complemented numeral point to obtain a product decomposition of slices and algebra categories. This is an additional application argument, not a repetition of the appendix's initial-image proof. Preserve it.
- The phrase “reversed conditional” is descriptive of the two branch equations used earlier; no new mathematical structure is needed. Where §7.1 has just written the branch behavior in full, calling the map “the required conditional” would suffice. This is optional terminology, not a correctness defect.
- `B_n(Q)` in the fiber proof abbreviates the appendix's `B_n(Q,q)` without saying so. The displayed slice context makes it recoverable. An economical repair is to say “the nullary summand of `H_E(Q)` is `R_0^E`” and subsequently “the pullback defining the summand of arity `n`,” avoiding additional abbreviation. It is not necessary to copy the appendix's defining pullback.
- In Theorem 7.6, `q=θ I(g)` is correctly typed in the total splitting, whereas `g` and `ℓ` belong to the syntactic partial-map category. Keep this distinction explicit.

No wholesale terminology substitution is indicated. The qualifications about standard indices, the chosen axiom predicates, partial source maps, and nonstandard proof codes affect the mathematics and should not be removed as empty prose. There is no need to add a disclaimer paragraph explaining that the constructions avoid mistakes.

## Scope

All three assigned source files were read in full. The relevant parts of §§3–5 and Appendix A were consulted for definitions and dependencies, including the actual general derivation-initiality lemma. Printed page locations were checked against the text extracted from the v22 PDF. This review did not recompile the manuscript or inspect newly rendered page images, verify every literature attribution in §§6–7, or certify mathematical correctness. The abstract and introduction were not revised or reviewed. No manuscript edits were made by this agent.
