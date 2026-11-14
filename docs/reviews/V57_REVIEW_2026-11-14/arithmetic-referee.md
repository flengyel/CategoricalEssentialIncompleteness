# Arithmetic and syntax referee audit — manuscript v57

Pinned source: `dfe6d3b9b948875d9d268ef8bbd332d65c6b53e5`.
Scope: §§6–8 and Appendix D. The accompanying `arithmetic-ledger.json` records every assigned numbered proof (30 results), its explicit hypotheses, hypothesis use, reconstruction, dependencies, and 10 central informal claims. Existing Lean status was not used as proof.

## (A) Kill-shots / hard blockers

No confirmed hard blocker was found in the assigned material. This is a scope-limited mathematical assessment, not an audit of all dependencies or a claim that the full manuscript is error-free.

The uniform sentence construction was checked in its order of quantifiers. The family predicate, source search index, Turing parameterization and total morphism `q` are chosen before the numeral `e` and before the consistency assumption on its selected theory. The consistency assumption is used only to rule out the two simultaneous provability alternatives (Theorem 8.6, p.41, `08b-uniform-independent-sentences.tex:4–90`). No effective choice of a consistency proof or model is needed to compute `q`.

## (B) Major weaknesses

No confirmed major proof gap was found. The proof of Lemma 6.1 is citation-dependent: its full PA-provable universal/specialization/composition identities are invoked from the chosen deterministic computation coding. The primary-source reviewer checked Montagna pp.108 and115 and found support for formalized s-m-n and the trace representation; those pages do not print each displayed identity verbatim. This is recorded as a source-verification limit, not a demonstrated mathematical error.

The arithmetic associated-category corollary (8.10, p.50) was verified as an application of the stated general theorems. Its correctness remains conditional on the independent checks of §§4–5 assigned to other reviewers.

## (C) Minor issues

No concrete wording defect requiring a mathematical correction was confirmed in the assigned proof text. The audit did not convert harmless use of defined terms, including `parameter`, `code`, `partial`, or `total`, into terminology findings.

Theorem 6.9 retains the surrounding consistency assumption on `T`, while its construction and leastness proof do not visibly use nontriviality. This is an inherited restriction of scope, not a false assertion or a reason to weaken the result during this audit.

## (D) Cross-section consistency failures

No confirmed cross-section consistency failure was found in the assigned material. The following potentially dangerous distinctions were checked explicitly.

1. **Indices and classes.** `S_T` uses indices modulo universal `T`-provable graph equality; `Rec` uses extensional equality of standard partial functions. The model functors and numerical comparison use their respective equality relations. Arbitrary recursive separators in Corollary 8.4 only need partial source representatives; the proof does not assume their totality is provable in PA.
2. **Code models and semantic structures.** `N` and `M=N^I/U` interpret syntax/program objects. `K` interprets decoded standard formulas. Theorem 7.9 transports a subobject and factorization by ultrapowers; it does not assign external meanings to nonstandard formula codes.
3. **Internal and external consistency.** Theorem 8.3 obtains `K` from external consistency and completeness. Lemma 8.9 proves the signed theory internally consistent using a finite Boolean valuation constructed from the two candidate derivations and verified by PA induction. These are separate arguments for separate theories.
4. **Internal initiality.** Propositions 6.5–6.6 and Lemma 6.8 prove their totality and uniqueness statements by induction in `T` on coded size/length. Proposition 8.5 separately proves that numeral reindexing preserves the particular initial algebra using a complemented slice decomposition.
5. **Source and target inseparability.** Appendix D proves source inseparability while acknowledging that the family target has Boolean restriction lattices and separators. Its cardinality argument shows that the image of the Turing morphism is not Turing there. No inference from image separators to source separators is made.

### Functional outline and dependency check

| Unit | Function | Dependency chain |
| --- | --- | --- |
| §6 | Build categorical computation and internal finite deduction | PA computation identities → witness search → predicate/splitting equivalence → parameterized syntax/lists → substitution → derivation initiality → generated theories |
| §7 | Supply model interpretation and semantic consistency | Graph interpretation → regular total functor; finite standard syntax → substitution soundness → validity in `K`; ultrapower/Łoś comparison → transported disjointness |
| §8 | Prove arithmetic incompleteness and uniformity; construct numerical and signed-theory instances | Diagonal reductions + search lift + semantic consistency → incompleteness; complemented family fibers + one parameterization → uniform independent sentence; numerical comparison → concrete domains; Boolean valuation → signed-theory instance |
| Appendix D | Explain faithful families and theory extension | Completeness/LS → faithful coordinate family; singleton tests → local connectedness and weak choice; quotient hom-surjectivity → Turing preservation; standard truth → `S_Th(N)≅Rec` |

The literal organization matches these functions. The arithmetic/signed-theory distinction is maintained in the later corollary rather than treating the arbitrary arithmetical theory as automatically internally consistent.

## (E) Acceptance conditions, non-negotiable

1. Retain the explicit distinction between code interpretations and semantic structure `K` in any revision of §§7–8; the verification endpoint is the typed factorization and the standard-code restriction. An extension to semantic interpretation of arbitrary nonstandard codes would require a new argument.
2. Retain the choice order in Theorem8.6: one `q` before `e` and consistency. A revised statement requiring a family depending noncomputably on consistency would not establish the printed uniform result.
3. Resolve any blocker from the independent §§4–5 audit before accepting Corollary8.10; that corollary depends on their full hypotheses and conclusions.
4. If exact formalization coverage is claimed, verify the printed statements against a pinned Lean revision independently. This mathematical reconstruction does not establish those code claims.

No repair of an assigned theorem is demanded by this audit. The conditions above preserve the endpoints actually checked, and identify material outside this review rather than adding unprinted hypotheses.

## (F) Not checked / uncertainty log

- All 30 assigned numbered proof environments and their local definitions were read. The ledger records 3–5-step reconstructions and hypothesis use for each. Ten central informal claims were also checked or marked as source-dependent.
- The manual `mathematical-writing.txt` was read sequentially through lines1–1400, covering the opening material through the start of §13. The full-manual writing judgment belongs to the dedicated writing reviewer; this report makes no claim that this reviewer read the entire manual.
- The chosen computation coding was examined at its mathematical interface; its simulator/compiler correctness was not independently rebuilt. Montagna's cited original pages were checked by the primary-source reviewer as described in(B).
- Bernardi's original pp.125–126 and the claim that the precise displayed PA equivalence is his example were not independently read. This comparison is not used to prove the manuscript's arithmetic incompleteness theorem.
- No Lean build, transitive axiom audit, or registration verification was performed by this reviewer.
- No independent proof of the general §§4–5 theorems is claimed here.

Strongest confirmed blocker: none in the assigned material. Strongest suspected unconfirmed blocker: none supported by a concrete failed inference. Most important item not checked: the complete general associated-category transfer theorem used by Corollary8.10. The whole-paper recommendation depends on those other assigned reviews. Final recommendation for the whole paper: **unknown from this scope**; the assigned arithmetic arguments have no identified substantive defect.
