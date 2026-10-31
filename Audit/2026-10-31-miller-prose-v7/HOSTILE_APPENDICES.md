# Final disposition after the v7 source check

The five local findings C1–C5 are resolved in `manuscript/essential_incompleteness_via_local_connectedness_v7.tex`. The v7 source explicitly types the two-variable component computation (lines 2177–2181), states preservation of restrictions for both splitting equivalences (2239–2264), identifies the propositional theories componentwise (2440–2441), states the no-upper-bound example existentially (2759–2762), and restores lowercase `$p$` in the Di Paola–Montagna title (2927–2931).

The four suggested economy edits are also implemented: the Appendix A roadmap is removed, the semigroup extension is denoted by `\widehat f`, the Boolean-tautology argument is shortened, and Appendix C opens with its mathematical conclusion. None of C1–C5 remains an outstanding condition. The v6 findings below are retained as the record of the changes requested.

This was a focused source check of those dispositions, not a second review of the complete manuscript or a PDF-layout check. New Sections B.3–B.4 are assessed separately in `tmp/proof_object_initial_audit.md`. No manuscript file was edited in this pass.

# Appendices A–C and bibliography: original v6 audit

Reviewed source: `output/pdf/essential_incompleteness_via_local_connectedness_v6.tex`, lines 1737–2788. Line references below refer to that unmodified source. The review covers every sentence in the assigned portion and checks the definitions imported from the main text when needed. No mathematical hard blocker was found in these appendices. The most useful changes are local precision and shortening; several apparently repetitive qualifications protect actual distinctions and should remain.

The governing prose sources consulted were Knuth–Larrabee–Roberts, *Mathematical Writing*, §1 (Stanford report, printed pp.1–6), and Heller (1990), Introduction and §§1–3 (printed pp.1252–1257). The former supports explicit first-use definitions, stable notation, connected proofs and readable sentences. Heller's relevant example is direct passage from typed data to equations and their consequences. His personal remarks and rhetorical asides are not a reason to add such remarks here.

## (A) Kill-shots / hard blockers

None confirmed in the assigned text. In particular, the following arguments survive the stated definitions:

- The cosheaf equivalence uses the only nontrivial covering condition, the pushout over `{c}`.
- Componentwise c.e. images provide regular images in the fork functor category. The descent argument proves naturality after quotienting by a componentwise surjection.
- The partial-map category has componentwise restrictions and ranges; its weak-choice proof uses inverse components of injective partial functions, so it does not presume arbitrary natural sections.
- The Turing morphism checks both endpoint computations before returning a central component. Its domain is a subfunctor, and specialization gives the required natural total parameter map with equality of domains.
- The finite-proof construction is c.e., natural under atom relabeling, and consistent componentwise.
- Appendix C's domain enlargement retains ordinary recursive extensions. Its Turing morphism has a K-c.e. domain and an ordinary partial recursive extension. The exhibited separator cannot have a source switch, and the two displayed compatible arrows have no common upper bound.

These are proof checks, not a claim of formal verification.

## (B) Major weaknesses

None confirmed in the assigned text. No new assumptions or reconstruction of an appendix are required by this audit.

## (C) Minor issues

### C1. Unclear quantification in the domain statement

- **Anchor:** Appendix A, proof of Theorem `thm:fork-turing`, lines 2218–2222: “`tau_i(c_i(y_i),v_i)`, for `v_i in V_i`, has domain exactly `D_i`.”
- **Failure mode:** ambiguous.
- **Reason:** `D_i` is a subset of `Y_i x V_i`, but the sentence singles out only `v_i` as varying. The intended two-variable function is already used correctly in the proof; the sentence should name it.
- **Evidence:** typing/derivation from lines 2181–2186.
- **Replacement:**

  ```latex
  At component $i\in\{1,2\}$, equations
  \eqref{eq:fork-turing-endpoint} and
  \eqref{eq:fork-specialization} show that the partial function
  \[
    (y_i,v_i)\longmapsto\tau_i(c_i(y_i),v_i)
    :Y_i\times V_i\rightharpoonup V_i
  \]
  has domain $D_i$ and agrees there with $F_i$.
  ```

- **Impact/severity/repairability:** local exposition; minor; direct replacement. No theorem changes.

### C2. State preservation of restrictions in the splitting equivalence

- **Anchor:** Appendix A, Proposition `prop:fork-recursion`, lines 2272–2287; later use at lines 2320–2322.
- **Claim as written:** the constructed functor is fully faithful and essentially surjective; the later invariant argument treats the result as a restriction equivalence and passes to total maps.
- **Failure mode:** unproved, locally.
- **Reason:** the construction does preserve restrictions, but the proof lists only the ordinary equivalence properties. One domain equation makes the precise structure used later explicit.
- **Evidence:** derivation. For `f=dfe`, the map `r_d` is defined on every value of `f`; hence the restriction domain of `r_d f m_e` is the inverse image under `m_e` of the domain of `f`.
- **Insertion after line 2283:**

  ```latex
  It preserves restrictions, since
  $\overline{r_d f m_e}=r_e\bar f m_e$.
  ```

  For the numerical equivalence at lines 2290–2302, add “It also preserves restriction domains.” before its final sentence, or replace that sentence by “Thus this is a restriction equivalence.”
- **Impact/severity/repairability:** makes the later passage to total categories explicit; minor, not a failure of the construction; direct insertion.

### C3. Identify the ordinary propositional theories componentwise

- **Anchor:** Appendix B, Theorem `thm:fork-proof-presentation`, line 2480: “In particular, this gives a consistent theory in classical propositional logic.”
- **Failure mode:** ambiguous.
- **Reason:** the construction has three syntax carriers and three conclusion sets assembled into one functor. The ordinary classical theories occur at the components. The preceding categorical assertion already states consistency of the restriction idempotent.
- **Evidence:** construction of `S_j` and `Prf_j`, followed by the componentwise valuation proof at lines 2502–2528.
- **Replacement:**

  ```latex
  At each component, these conclusions form a consistent theory of
  classical propositional logic.
  ```

  Deleting the sentence is also mathematically safe, since its content is already expressed by the consistency equation; the replacement better explains the ordinary-logical meaning.
- **Impact/severity/repairability:** distinguishes the functor from its component theories; minor; local replacement.

### C4. Replace the modal wording by the existential claim proved

- **Anchor:** Appendix C, Proposition `prop:missing-lift`, lines 2585–2588: “two parallel arrows ... whose restriction idempotents are disjoint can have no common upper bound”.
- **Failure mode:** ambiguous.
- **Reason:** “can have” is an indirect expression of the existential statement; the proof gives two specific arrows.
- **Evidence:** the witnesses `i_1 1_A` and `i_0 1_{A^c}` at lines 2716–2721.
- **Replacement:**

  ```latex
  Moreover, there are parallel arrows in $\mathcal C_K$ with
  disjoint restriction idempotents and no common upper bound in the
  restriction order, although finite joins of restriction idempotents
  exist.
  ```

- **Impact/severity/repairability:** precision of the stated conclusion; minor; local replacement.

### C5. Preserve the lowercase p in the cited title

- **Anchor:** bibliography, `DPM`, lines 2754–2756: “syntactic `$P$`-recursion categories”.
- **Failure mode:** inconsistent_use (bibliographic transcription).
- **Reason:** the primary article's title uses lowercase `p`, including on its printed title page, whereas the bibliography capitalizes it. A cited title should retain the source notation even when the manuscript uses `P` elsewhere.
- **Evidence:** supplied `upload/PaolaMontanga-PropertiesSyntacticpRecursion-1991.pdf`, printed p.643; extracted text at `tmp/pdfs/PaolaMontanga-PropertiesSyntacticpRecursion-1991.txt`, and the Cambridge publisher title.
- **Replacement:** `$p$-recursion categories`.
- **Impact/severity/repairability:** bibliographic accuracy only; minor; one-character correction.

### Optional economy, not errors

These are editorial choices rather than mathematical defects. They should not be used to pad a count of errors.

1. **Lines 1739–1742:** the appendix opening announces that it will prove the assertions in the main text. It can be shortened to “We construct the frame and Turing morphism of $\mathscr R_X$.” The existing paragraph is a normal roadmap, not LLM-facing process commentary.
2. **Lines 2044–2048:** use `\widehat f:Y^\#\to M` for the semigroup extension instead of `f^\#`, since `(-)^\#` has just been introduced as the word functor. Both existing types are explicit, so this is an avoidable overload rather than an ill-typed map.
3. **Lines 2513–2524:** the clause-by-clause check that the three Hilbert schemes are tautologies is elementary and ends with the vague sentence “These observations give the displayed implications in all Boolean cases.” A concise replacement preserving the entire argument is:

   ```latex
   The three logical schemes are Boolean tautologies, and modus
   ponens preserves truth. Induction on $p$ and $q$ would therefore
   make $\varphi$ and its negation both true, a contradiction.
   ```

   This is consistent with the intended research audience and Heller's concise proofs. Retain the finite valuation construction preceding it: that is the actual consistency argument.
4. **Lines 2534–2537:** replace the two-sentence roadmap by “The lifting hypothesis in Theorem~\ref{thm:local-lifting} cannot be omitted, even for a faithful range functor that preserves restriction products and reflects zero arrows.” This states the appendix's conclusion directly.

## (D) Cross-section consistency failures

No conflicting definitions were found in the assigned portion. C2 and C3 identify local statements worth making more explicit; they do not establish contradictory uses.

### Verified dependencies and definitions

- `receives`, range, agreement, restriction splitting, partial monomorphism, section, weak choice, and recursion category are defined in the main text before their appendix uses.
- The components of `V` and the maps `r_i^V` are defined in equation `eq:universal-fork`; the coordinates `(k,z,a,b)` used in the frame and equality arguments refer to that definition.
- “Frame” is defined in the main text by the three isomorphisms and their inverses, with Heller §3 cited; it is not an undefined label in Appendix A.
- `C_rec` has c.e. numerical carriers and functions computed by partial recursive programs total on the indicated carriers. Uses of partial recursive inverses on c.e. images conform to that convention.
- Appendix C explicitly distinguishes a function's chosen K-c.e. domain from the domain of its ordinary recursive extension. The formula for `f_{e,a}` gives the actual intersection domain. This explanation is essential and should remain.
- Appendix C distinguishes joins of restriction idempotents from joins of arbitrary compatible arrows. Its last example proves a genuine difference; the qualification is not defensive prose.
- The cosheaf example showing that the value at `X` need not preserve products or monomorphisms prevents a real confusion about partial-map domains; retain it.

### Actual appendix outline and functions

| Part | Function |
|---|---|
| A.1 Cosheaves and functor categories | Identify the cosheaf category; prove finite limits, images and extensivity of the numerical fork category. |
| A.2 Partial maps, ranges and connected restrictions | Prove the partial-map structure, weak choice and local connectedness. |
| A.3 Universal object and frame | Embed every object into `V`; give the product, coproduct and word isomorphisms. |
| A.4 Turing morphism | Construct compatible numerical component computations and prove their parameterization property. |
| A.5 Recursion category and splitting | Extract the isotypical full subcategory; prove the splitting equivalence and nonnumerical invariant. |
| B.1 Syntax algebra | Construct the formula functor and prove its initial-algebra property. |
| B.2 Proof object and range | Construct finite derivations, obtain the least deductively closed conclusion subfunctor, and prove consistency. |
| C | Exhibit a range functor satisfying the other lifting-theorem hypotheses while the indicated pair is separable. |
| Bibliography | Supply sources used in the body and appendices. |

No reorganization is recommended. The dependency order is appropriate.

## (E) Acceptance conditions, non-negotiable

For this appendix pass, apply C1–C5 or equivalent precise repairs. These are local changes; none requires dropping a theorem or rejecting the mathematical construction. Preserve the displayed types, domain equalities and nonpreservation examples while shortening prose.

The final source should compile with resolved cross-references after the edits. Compilation and page-layout checks belong to the integration pass, not this source-only review.

## (F) Not checked / uncertainty log

- No new Lean or executable formalization was checked.
- No rendered v6 or v7 PDF was inspected during this appendix pass.
- The main body was read selectively to resolve imported definitions and the exact hypotheses used by the appendices, not reviewed sentence by sentence here.
- Bibliographic metadata was checked against the supplied primary Heller and Di Paola–Montagna PDFs, and current primary publisher/author records for the Miller, Bauer–Hanson, Curry and Bernardi entries. This pass did not independently reopen every bibliographic item or the pinned Corrections repository URL.
- No independent priority claim is assessed by this appendix review.

Strongest confirmed issue: the splitting-equivalence proof should explicitly state preservation of restrictions before its use to compare total categories (C2), a short omitted verification already supplied by the displayed construction. Strongest suspected unconfirmed blocker: none identified in the assigned text. Most important item outside this review: the complete main-theorem and application audit. The recommendation for the entire manuscript necessarily depends on that other material. Final recommendation: **unknown** for the whole manuscript; the assigned appendices require only the local revisions above.
