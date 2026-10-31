# Bounded hostile review of the integrated v9 changes

**Source:** `manuscript/essential_incompleteness_via_local_connectedness_v9.tex`, 3,350 lines, SHA-256 `c71c7a10ba6df6f3c9657a71e7808417d0ce3330c99dede337e89e3668cc4831`.

**Scope:** comparison with the integrated v8 source, followed by direct reading of the changed definitions, equations, and their immediate dependencies. The review covers the term algebra and Montagna comparison, binary representations, numerical word codes, `J_rec`, and the altered proof-object wording. It does not reprove all theorems. No manuscript edits were made.

## A. Confirmed hard blockers

None found in the reviewed changes. No counterexample to an asserted result, ill-typed new equation, or weakened central hypothesis was established.

## B. Object and equation checks

- **Term algebra and index families, §5.** `O` consists of closed terms with syntactic equality; `|X|` is a separately assigned set. The recursive formulas for `γ_X` have the indicated domains, including the explicitly defined order of the coproduct tags. `I(X,Y)=N` is a hom-index family; the source and target remain part of an arrow's type. Composition uses the same PA-provable graph identity as v8.
- **Montagna comparison, §5.** `Π_T` is given on objects and arrows. The displayed bijections on hom-sets use the same provable graph equivalence, and every declared set object is in the object image. This establishes the asserted equivalence without equating a formal term with its assigned set. Montagna's supplied p.105 describes the actual-set objects and the same tagged-union convention. The paper's explicit coding choices are retained.
- **Binary representations, §§4.1–4.2.** The new terminology retains the map `ρ`, its fibers `P_z`, and all quantifiers over those fibers. The displayed types of `τ_z`, the metric, `δ`, `g`, and `r_e` agree with their formulas. The exact-output search remains separately indexed by `m`. The cut reduction and the separator still use the same underlying sets and computations. The final wording explicitly distinguishes an oracle program from its numerical index `d`.
- **Word codes, §9 and Appendix A.4.** `A#` is now a numerical set of codes. The structure maps decode, apply the original component map, and encode. The `code_4` and `code_2` outputs in the frame proof lie in the stated components; their naturality follows because both paths encode the same sequence of projected entries. The inverse construction recovers the same length and coordinate sequences. The final ambient-exponent and source-domain conventions are checked in C below.
- **`J_rec`, §8 and Appendix A.5.** The rename distinguishes the carrier functor from the indexing category `J`. Its uses in the numerical pair category and in `hat(f)=γ_Y J_rec(f)γ_X^{-1}` are consistent. The latter is a partial function `N⇀N`, as required by the numerical splitting comparison.
- **Proof objects, §§4.3 and 8 and Appendix B.** `Prf_T` is explicitly a set of numerical codes of finite derivation trees. Relabeling preserves axiom-leaf validity through the stated subset inclusions and preserves modus-ponens matching through the constructor equations. The arbitrary algebra values are described by equations under `q_j`, not called proofs. The conclusion fiber and its range remain distinct. The final arrow/subset wording corrections likewise distinguish partial identities from the unions or domains on which they act.

## C. Resolved presentation qualification

The final source fixes `m(A)` for each unchanged numerical carrier object `A`, with `m(V_0)=4` and `m(V_1)=m(V_2)=2`, before defining `A#` (lines 1680–1697). Thus the chosen object coding is unambiguous and agrees with the frame's `code_4` and `code_2` formulas.

For `f:Y⇀Z`, the component domain of `f#` is now explicitly the set of `code_{m(Y_j)}`-codes whose entries lie in `(D_f)_j` (lines 2309–2318). This is a subset of `(Y#)_j`; it does not incorrectly identify that subset with the separately coded object `(D_f)#`. The domain is stable under the structure maps because `D_f` is a subfunctor. Decode/apply/re-encode preserves identities and composition, including their domains. This resolves the earlier qualification without changing the objects of `C_rec` or adding a global compatibility requirement on codings of subsets.

No correction remains requested in this bounded pass.

## D. Preserved definitions and results

A direct source comparison verified that the complete range-functor definition, including preservation of restrictions, ranges, zeros, and binary restriction coproducts, is **byte-identical to v8**. Its meaning is taken from the user's explicit definition; no weaker literature convention has been substituted.

The statements labeled `thm:local-lifting`, `prop:disjoint-joins`, and `cor:domain-incompleteness` are also byte-identical to v8. All original labels remain in the same order. The reformulated Miller conclusion now names the partial identities on the theorem and refutation sets; its consistency and semidecidability hypotheses are retained. The new `b=Q_{PA,T}(b_0)` in the syntactic application has source `U` and target `U+U` in `S_T`, with the isomorphism supplied by the stated functor.

## E. Disposition

The reviewed changes introduce no confirmed substantive defect. They make the representations and arrow types more explicit while preserving the central hypotheses and conclusions. The only earlier presentation qualification is resolved in the final source.

## F. Limits

This is an independent local change review, not a whole-paper correctness certificate, a new literature-priority review, or a Lean audit. The standard arithmetization facts remain the cited Montagna dependencies. No compilation, PDF visual inspection, or repository operation was performed by this reviewer. The source hash identifies the final integrated version actually inspected, including the ambient-exponent fix, explicit source-coded word domains, proof-code and arrow/subset wording, layout changes, and revised relabeling paragraph. The unchanged range-functor definition and three central statement comparisons were rerun against this final source.
