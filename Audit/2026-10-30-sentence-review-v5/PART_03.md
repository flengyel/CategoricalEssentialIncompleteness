## (A) Kill-shots / hard blockers

None confirmed in this scoped terminology, definition-order, and typing review. The range-functor theorem's source and target categories are explicitly typed, its lifting requirement concerns complementary source pairs, and its proof applies the functor to a source equation before taking inverse images in the target. The reviewed text does not assume that the general range functor preserves products or that the source lift is total.

This is an author-side audit of immutable `build/sentence-review/baseline.tex`, lines 519–815 (Section 6), not an external referee's confidential evaluation. Every sentence, formula, proof passage, and heading in the assigned range was read. The block coverage record contains all 24 blocks beginning in that range, B052–B075.

## (B) Major weaknesses

None confirmed within the assigned issue axes. Four local issues are recorded below. They do not establish that any theorem is false.

## (C) Minor issues

### P03-01 — An ambiguous antecedent gives a false reading of the opposite-summand case

- **Anchor:** PDF p. 8, Proposition 6.2 proof, source lines 585–586, block B057: “the two equalities force both these restricted arrows to be zero.”
- **Claim as written:** After discussing `\theta\gamma` and `\theta'\gamma` lying in opposite summands, “both these restricted arrows” are said to be zero.
- **Failure mode:** `ambiguous`.
- **Why it fails as written:** The phrase can denote the two morphisms `\theta\gamma` and `\theta'\gamma` just placed in summands. Those need not be zero. The proof needs the composites with `a+b` to be zero. Both kinds of restricted morphism occur in the immediately preceding sentences, so the antecedent is not fixed by the text.
- **Evidence:** `counterexample` to the first reading. In `\mathbf{Pfn}`, take singleton sets `X=\{x\}` and `Y=\{y\}`, let `a=b=0_X`, so `p=0_{X+X,X}`, and let `\theta(y)=i_0x`, `\theta'(y)=i_1x`, and `\gamma=1_Y`. Then `\gamma` is connected, `p\theta=p\theta'=0`, and the two displayed equations in the proof hold. Nevertheless, `\theta\gamma` and `\theta'\gamma` are nonzero. The composites `(a+b)\theta\gamma` and `(a+b)\theta'\gamma` are zero. This is a small counterexample to an ambiguous reading, not a counterexample to Proposition 6.2; minimality is not claimed.
- **Downstream impact:** A reader can misread a step in the proof of the proposition supplying the target sections for Theorem 6.3.
- **Severity / repairability:** Minor; directly repairable by naming the morphisms.
- **Concrete repair:** Replace that sentence with:

  ```latex
  If $\theta\gamma$ and $\theta'\gamma$ lie in opposite summands,
  the two displayed equalities give
  $(a+b)\theta\gamma=(a+b)\theta'\gamma=0$.
  ```

- **Writing basis:** KLR §1, point 17, applied to a genuinely ambiguous referent; point 14 also supports explicit identification of the same morphisms across sentences.

### P03-02 — The notation `c_M,c'_M` is undeclared

- **Anchor:** PDF p. 9, Lemma 6.5 proof, source line 728, block B068: `\nabla_{X_M}(c'_M+c_M)`.
- **Claim as written:** This expression is the partial injection whose inverse is the interpreted selection program.
- **Failure mode:** `missing_definition`.
- **Why it fails as written:** Section 4 defines `X_M` and the functor `F_M:S_T\to\mathbf{Pfn}`; Section 5 defines `F_T(c)` componentwise using `F_M(c)`. No convention `c_M:=F_M(c)` or `c'_M:=F_M(c')` is declared. A search of the complete baseline finds this as the only occurrence of these two symbols. The nearby predicates `C,C'` and their truth sets make it especially useful to distinguish the partial identity morphisms from their defining subsets.
- **Evidence:** `absence_in_text`, checked against the complete baseline, together with the positive definitions of `F_M` at source lines 399–411 and `F_T` at lines 450–454.
- **Downstream impact:** Local ambiguity in the comparison between the interpreted program and the target section; the functor itself is adequately defined.
- **Severity / repairability:** Minor; no new notation is necessary.
- **Concrete repair:** Replace the expression by

  ```latex
  $\nabla_{X_M}\bigl(F_M(c')+F_M(c)\bigr)$.
  ```

  The resulting partial morphism has type `X_M+X_M\rightharpoonup X_M`.
- **Writing basis:** KLR §1, points 11 and 14: introduce symbols and keep the interpretation notation consistent. This is not a claim that the model functor is missing.

### P03-03 — Coproduct injections are silently reused as arithmetic coding terms

- **Anchor:** PDF p. 9, Lemma 6.5 proof, source lines 713–720, block B067: “returning the tagged input `i_1x`” and the arithmetic graph equation containing `z=i_1x` and `z=i_0x`.
- **Claim as written:** The displayed formula is a formula whose equivalence with `G_{e_s}` is proved in arithmetic.
- **Failure mode:** `inconsistent_use` / `ambiguous`.
- **Why it fails as written:** The preliminary definition declares `i_0,i_1` as categorical coproduct injections. In `S_T` these are morphisms represented by program indices. The proof then uses the same notation for numerical tag-construction values inside an arithmetic formula, without declaring this local interpretation. The general choice of numerical codings in Section 3 makes the intended encoding available; it does not explicitly identify this use of `i_jx` with that encoding. This is a missing notational bridge, not a claim that the tagged coding cannot be represented in PA.
- **Evidence:** `structural_argument`: compare the typed injections in Section 2 (source lines 236–237), the index/graph convention in Section 3 (303–307), and the object-language equality in line 720. A whole-baseline search finds no declaration that `i_jx` denotes the chosen numerical tag code in arithmetic formulas.
- **Downstream impact:** The boundary between a morphism in the quotient category and its numerical coding operation is blurred at the formalized graph calculation.
- **Severity / repairability:** Minor; repairable by a single local convention before the first use.
- **Concrete repair:** Before “Search increasing finite bounds…”, add:

  ```latex
  Here $i_jx$ denotes the fixed numerical code of $x$ in summand $j$.
  ```

  If the author prefers to avoid overloading, use separately declared tag-coding symbols in the arithmetic equation; the one-sentence convention is the smaller repair.
- **Writing basis:** KLR §1, points 11 and 14, and the mathematical-writing skill's distinction between an index, a represented morphism, and an object-language expression.

## (D) Cross-section consistency failures

### P03-04 — The informal incompleteness bridge leaves the extension correspondence implicit

- **Anchor:** PDF p. 10, paragraph after Corollary 6.7, source lines 801–808, block B074: “The corollary therefore proves essential incompleteness whenever the theories under consideration have such representations by restriction idempotents and the two inequalities hold for the base theory.” Compare the explicit conclusion for `t\ge t_0` in lines 780–782, and the definition of essential incompleteness in the Introduction, lines 110–111.
- **Claim as written:** Representing theories by restriction idempotents, plus the two base-theory inequalities, is said to yield essential incompleteness.
- **Failure mode:** `ambiguous`.
- **Why it fails as written:** Corollary 6.7 applies to extensions represented by `t\ge t_0`. The explanatory paragraph does not explicitly include that correspondence between theory extension and the order on representing idempotents. Moreover, the earlier logical use of “essentially incomplete” quantifies over consistent c.e. extensions, whereas this paragraph has an unspecified class of represented theories. The later arithmetic and propositional applications supply the missing correspondence concretely; those later constructions should not serve as an undeclared definition of the generic claim here.
- **Evidence:** `structural_argument`: the corollary's quantifier is expressly over `t\ge t_0`, while the explanatory sentence states only existence of representations and base inequalities. The complete-source search found later explicit constructions: the arithmetic inclusion `t_{\PA}\le t_T`, and the propositional definition of an extension as `t\ge t_0`. Thus the issue concerns this bridge sentence, not the demonstrated applications.
- **Downstream impact:** The categorical conclusion can be read as a logical essential-incompleteness theorem without first identifying which extensions the representation covers.
- **Severity / repairability:** Minor exposition/scope issue; no counterexample to Corollary 6.7 is asserted.
- **Concrete repair:** Keep the sentence interpreting the two equations, then replace the following sentence by:

  ```latex
  If extensions of the base theory are represented by restriction
  idempotents $t\ge t_0$, the corollary rules out a complete consistent
  extension in this class.
  ```

  The logical application in Section 7 can continue to assert essential incompleteness for all consistent c.e. extensions, where the required representation and inclusions are constructed.
- **Writing basis:** KLR §1, points 5, 11, and 17, applied to preserving the actual quantifier and clarifying the semantic interpretation of the formal result.

## (E) Acceptance conditions, non-negotiable

For approval of the wording in this assigned range, the verifiable endpoints are:

1. **Proposition 6.2:** Replace the ambiguous “both these restricted arrows” with the two composites with `a+b`; the opposite-summand sentence must be true on the stated singleton test. Leaving the ambiguity prevents terminology/typing approval of this proof passage, but does not establish rejection of the proposition.
2. **Lemma 6.5:** Define `c_M,c'_M` before use or use `F_M(c),F_M(c')`; the rendered comparison must contain no undeclared coordinate morphisms. Leaving it prevents completion of this notation pass.
3. **Lemma 6.5:** Declare the numerical interpretation of `i_jx` before it is used in the program and arithmetic graph equation. The endpoint is a clear separation between a categorical injection and its chosen code-level operation. Leaving it prevents completion of this definition-order pass.
4. **Corollary 6.7 interpretation:** State that represented extensions correspond to `t\ge t_0` and identify the class of extensions under discussion, or limit the sentence to the exact categorical conclusion. If this correspondence is not supplied, drop the unrestricted generic essential-incompleteness inference from this paragraph; the applications may retain their separately established claims.

No major reconstruction or deletion of a theorem is required by a confirmed finding in this report.

## (F) Not checked / uncertainty log

**Read and searched.** Read every sentence and formula of source lines 519–815; also read lines 1–518 to locate all prior definitions used in Section 6. Searched the complete baseline for `c_M,c'_M`, the coordinate and injection conventions, sentence-object/negation terminology, extension representations, the lifting notation, and the relevant functor symbols. Consulted the baseline's PDF text, pp. 7–10, for page anchors. The immutable source and page text were not edited.

**Adequate definitions and uses.** Restriction idempotents, their order, disjointness, complements, inseparability, inverse image, ranges and their agreement law, restriction splitting, restriction products, pairing, diagonal, coproduct injections, copairing, codiagonal, range functors and `\chi`, connectedness, partial monomorphisms, sections, weak choice, and Turing morphisms are all defined before their formal use here. The names “switching,” “test arrows,” and “lifting” function descriptively; the actual maps and lifting equation are stated. No separate mathematical operation needs to be invented for these headings. The use of joins for parallel morphisms in Proposition 6.4 is explicitly tied to the already defined restriction order, so it is a standard order-theoretic use, not an undefined new join structure. No categorical synonym “domain,” “transition map,” or “structure map” occurs in the assigned range.

**Typed functors and maps.** The range functor in Theorem 6.3 has signature `F:\mathscr R\to\mathcal A`; Proposition 6.4 has `F:\mathcal C\to\mathcal A`. Their variance and preservation data come from the earlier definition. `F_M:S_T\to\mathbf{Pfn}`, `F_T:S_T\to\mathcal D_T`, and `Q_{T,T'}:S_T\to S_{T'}` have explicit preceding object and morphism assignments and composition checks. The canonical inclusion into `Split(\mathscr R)` is determined by the earlier explicit restriction-splitting definition; its object assignment is stated in the concluding paragraph. I did not treat these named canonical functors as missing definitions merely because their earlier data are not repeated.

**Scope limits.** This is a terminology, definition-order, and typing audit. The proof manipulations were read for their stated meanings and types; a new general correctness proof, exhaustive search for counterexamples to all results, and novelty/source-priority research were not undertaken. The singleton test was introduced solely to resolve the concrete antecedent issue in P03-01. The supplied KLR §1 excerpt (points 1–19, printed pp. 1–3 / PDF pp. 3–5) and the two specified skills supplied the editorial method; this is not a claim to have consulted all of KLR.

**Final self-audit.** Strongest confirmed blocker: none. Strongest confirmed local defect: P03-01's ambiguous zero claim has a demonstrably false reading. Strongest suspected unconfirmed blocker: none identified in this scope. Most important unchecked matter: full mathematical correctness beyond the types and local calculations reviewed here. The local findings do not depend on unavailable material. Overall manuscript recommendation: **unknown**; the present report resolves only the assigned terminology/definition-order scope and requires the four local repairs above for wording approval.
