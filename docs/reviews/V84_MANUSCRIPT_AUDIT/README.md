# Manuscript v84 audit

The manuscript readings support the separation criterion in Corollary 4.8 and the section-lifting counterexample in Proposition C.1. Two assertions still lack Lean evidence at their printed hypotheses. The last full kernel and axiom receipt covers v81. The v84 consecutive-clean count is **0 of 2**.

| Evidence | Revision or scope |
|---|---|
| Manuscript and Lean sources read | [b7bf333810d653be90d2d1ce1678ad81345f98b3](https://github.com/flengyel/CategoricalEssentialIncompleteness/tree/b7bf333810d653be90d2d1ce1678ad81345f98b3). [103-page PDF](../../../manuscript/logical_consequence_and_essential_incompleteness_v84.pdf) · [Correspondence as fetched](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/b7bf333810d653be90d2d1ce1678ad81345f98b3/FORMALIZATION_STATUS_V84.md) · [Corrected correspondence](../../../FORMALIZATION_STATUS_V84.md#numbered-statements) |
| Mathematical readings | Abstract, §§1–10 and Appendices A–E, including the nested inputs of §8. [Outline, proof dependencies and source comparisons](EVIDENCE.md) · [Second reader’s manuscript-first reconstruction and subsequent declaration checks](INDEPENDENT.md) |
| Full Lean replay available | v81, [73c2e4fa2bc633a3af012b1c4f85a7882018f962](https://github.com/flengyel/CategoricalEssentialIncompleteness/tree/73c2e4fa2bc633a3af012b1c4f85a7882018f962). [Run report](../../V81_WSL2_LEAN_VERIFICATION_73c2e4f.md) · [Machine-readable kernel and axiom receipt](../../V81_WSL2_LEAN_VERIFICATION_73c2e4f.json.gz) |

## A. Hard blockers

| Findings at the reviewed revision | Count |
|---|---:|
| Mathematical errors found in the manuscript | 0 |
| Ambiguities in a mathematical statement or its use found in the manuscript | 0 |
| In-scope Lean omissions identified | 2 |
| Gaps found in the paper proofs | 0 |

The two omissions concern **the domain formulation of Corollary 4.8** and **one auxiliary reduction in the proof of Proposition C.1**. A missing v84 receipt is a separate verification condition. The incorrect status of the Corollary 4.8 correspondence row is a reporting error, corrected with this audit. These counts describe this reading and the exact-type comparisons below. A new kernel and axiom replay of all assertions remains outstanding.

## B. Major findings

**1. Corollary 4.8, pp. 19–20.** The words “Under the hypotheses of Theorem 4.7” encompass an arbitrary split restriction category $\mathscr S$. Its total category $\mathcal D$ is regular with disjoint, pullback-stable finite coproducts. Every monomorphism in $\mathcal D$ has a partial inverse in $\mathscr S$. The syntax and derivation hypotheses are as in Theorem 4.7. For disjoint subobjects $a,b$ with consistent generated theory, the paper proves an equivalence with inseparability in $\mathscr S$. A complete consistent extension pulls back along the atom morphism to a separator. Conversely, a separator gives a valuation on the singleton term domain whose true sentences form a complete consistent extension. [Theorem hypotheses](../../../manuscript/latex/sections/03b-internal-adjunctions.tex#L375) · [Corollary and proof](../../../manuscript/latex/sections/03b-internal-adjunctions.tex#L477)

The Lean subobject equivalence has the required scope. The cited restriction-domain equivalence takes `[HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C]`. The splitting instance for binary joins requires that instance in the category being split. The first missing formal inference is the application deriving the domain operations and separator predicate for $\mathscr S$ at the printed hypotheses. [Subobject theorem](../../../Lean/CategoricalEssentialIncompleteness/V46SignedSubobjectIncompleteness.lean#L71) · [Domain theorem](../../../Lean/CategoricalEssentialIncompleteness/V46SignedFirstOrderIncompleteness.lean#L24) · [Splitting instance](../../../Lean/CategoricalEssentialIncompleteness/RestrictionSplitting.lean#L139)

Indeed, if $\Phi_X:\operatorname{Sub}_{\mathcal D}(X)\simeq_o\operatorname{Idem}_{\mathscr S}(X)$ is the subobject/domain order isomorphism, the least upper bound of $e,f$ is $\Phi_X(\Phi_X^{-1}e\vee\Phi_X^{-1}f)$. Applying $\Phi_X^{-1}$ proves both upper-bound inequalities and leastness. It also carries the two bounds and the meet and join conditions of every proposed separator back to subobjects. The splitting of a recursion category inherits restriction zeros. In an arbitrary $\mathscr S$ as above, restriction zeros are represented by the spans $X\leftarrow 0\to Y$. Their composites are empty spans since $0$ is strict and its inclusions are stable under pullback. The restriction of an empty span is the empty endomorphism span. This supplies the mathematics for the full quantifier. [Order isomorphism](../../../Lean/CategoricalEssentialIncompleteness/V46RestrictionSubobjects.lean#L124) · [Span representation](../../../manuscript/latex/sections/04-theory-extensions.tex#L18) · [Separator transport](../../../Lean/CategoricalEssentialIncompleteness/V46RestrictionSubobjectInseparability.lean#L49)

**2. Proposition C.1, p. 95.** At “Fix any index $a_*$” the proof asserts $n\in K\iff\langle h(n),a_*\rangle\in A$. The formal statement `K_iff_reduction_A` uses second coordinate zero. For arbitrary $a$, put $q=\langle\operatorname{encode}(\mathrm{simulationCode}(n)),a\rangle$. Its first projection is the simulation code. On input $q$ this program runs $n$ on $n$ and returns zero upon termination. Thus $q$ has even diagonal output exactly when $n\in K$, for every $a$. The zero-coordinate instance suffices to prove that $A$ is nonrecursive. [Printed reduction](../../../manuscript/latex/appendices/c-section-lifting.tex#L179) · [Program, specialization and checked equivalence](../../../Lean/CategoricalEssentialIncompleteness/OracleDiagonalSeparator.lean#L34)

The proposition’s quantified conclusion already has a Lean proof. The restricted codiagonal has the specified section $s_A$ in partial functions. For an arbitrary $s$ with the prescribed two fibers, those fibers cover $\mathbb N$. A source lift would be total recursive, and its output tag would decide $A$. Such an $s$ may have a different second component from $s_A$. The tag argument applies to all these choices of second component. [Printed conclusion](../../../manuscript/latex/appendices/c-section-lifting.tex#L54) · [Specified section](../../../Lean/CategoricalEssentialIncompleteness/OracleMissingLift.lean#L60) · [Universal nonlifting](../../../Lean/CategoricalEssentialIncompleteness/V46MachineOracleTuring.lean#L154) · [Literal partial-function type](../../../Lean/CategoricalEssentialIncompleteness/V46ManuscriptComparisonChecks.lean#L86)

## C. Minor issues and mathematical writing

| Passage | Reading and disposition |
|---|---|
| Abstract, p. 1 | Retain the two theorem references. The abstract specifies the signed axioms, consistency, the quantifier over closed extensions in the same language and the proper-join criterion. The second reader preferred stating the slice theorem-point hypothesis there. Section 1 explains it and Theorem 5.3 gives its precise type. Expanding the abstract would repeat the introduction. [Abstract](../../../manuscript/latex/abstract.tex) · [Introduction](../../../manuscript/latex/sections/01-introduction.tex#L70) · [Slice hypotheses](../../../manuscript/latex/sections/04-theory-extensions.tex#L260) |
| Theorem 4.7, p. 18 | The reader noted that the adjunction uses subobjects in the total category. The partial-inverse hypothesis allows the domain interpretation in the following corollary. This stronger common setting is consistent with both results. [Adjunction](../../../Lean/CategoricalEssentialIncompleteness/V46SignedFirstOrderAdjunction.lean#L25) |
| Proposition 3.4, p. 11 | A common upper bound of the two tagged morphisms already gives a total conditional. The proposition explicitly constructs their join under a sufficient hypothesis. Appendix C proves that even a common upper bound can fail. The two statements agree. [Sufficient condition](../../../manuscript/latex/sections/03-sections-and-inseparability.tex#L158) · [Counterexample](../../../manuscript/latex/appendices/c-section-lifting.tex#L215) |

For definition order, §1 introduces the total category, the atom and negation morphisms and the signed axiom subobject before stating the adjunction in notation. Section 9 defines the oracle evaluator, precision test, binary representation and fiber before displaying (15). Appendix C introduces the diagonal and $A$ before the arbitrary-index reduction. These checks follow the distinction between a readable summary and a theorem with explicit hypotheses in Knuth, Larrabee and Roberts. [§1, items 5 and 11–15](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf#page=4)

## D. Cross-section consistency

The previous correspondence row for Corollary 4.8 said “Proved” under the full printed hypotheses while its own audit summary recorded the missing instance. Its revised status states the two Lean types. The WSL2 handoff now retains the general $\mathscr S$ of Theorem 4.7. Appendix E.2 points to the subobject theorem, and E.4 discusses the specified section. Both references describe the results they cite. [Fetched row](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/b7bf333810d653be90d2d1ce1678ad81345f98b3/FORMALIZATION_STATUS_V84.md#L207) · [Revised WSL2 statement](../../CODEX_WSL2_CEI_V84_LEAN_HANDOFF.md#corollary-48-under-the-printed-hypotheses)

## E. Acceptance conditions

The WSL2 return must give the exact domain equivalence and the two-variable halting reduction, with their checked types, transitive axioms and a full successful receipt naming the tested v84 commit. Reconcile the complete assertion inventory with that return. Two independent clean reports must concern identical manuscript, Lean, correspondence and verification inputs. Updating the correspondence in this audit leaves the count at **0 of 2**. [Return specification](../../CODEX_WSL2_CEI_V84_LEAN_HANDOFF.md#full-v84-replay-and-independent-readings)

## F. Verification limits

The recursive input walk matched all 80 numbered labels in order to the v84 table and the row keys in the v81 receipt. Only the text inside the numbered statement of C.1 changed from v81, modulo whitespace. The abstract, introduction, ambient hypotheses and steps outside numbered environments required separate reading. The unchanged Lean tree and old receipt identify previously tested proofs. They do not certify a v84 checkout. [Input and receipt comparison](EVIDENCE.md#edition-and-verification) · [Unnumbered assertion inventory](../V80_ASSERTIONS/unnumbered-coverage.md) · [v81 supplements](../V81_WSL2_ASSERTIONS/README.md)
