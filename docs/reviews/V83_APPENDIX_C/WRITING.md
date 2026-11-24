# Mathematical writing review of Appendix C

Appendix C states in its first sentence why Theorem 3.1 needs a lifting hypothesis. The reader learns only near the end *why the lift fails in this example*. The target can choose between two summands according to membership in a nonrecursive set. Every total source morphism is recursive in the chosen codings, so its output tag cannot make that choice. Put this reason before the oracle construction and state the nonlifting conclusion in Proposition C.1. The proof order can remain as printed. [Opening](../../../manuscript/latex/appendices/c-section-lifting.tex#L4) · [Proposition C.1](../../../manuscript/latex/appendices/c-section-lifting.tex#L45) · [Output-tag argument](../../../manuscript/latex/appendices/c-section-lifting.tex#L186)

## What a reader encounters

| Passage | Function in the argument | Editorial judgment |
|---|---|---|
| [§1.1](../../../manuscript/latex/sections/01-introduction.tex#L219) and [§3.2](../../../manuscript/latex/sections/03-sections-and-inseparability.tex#L177) | §1.1 identifies the counterexample to Lengyel (2006), Theorem 4.1. §3.2 directs the reader to a complementary separator whose conditional does not lift. | Keep both pointers. Appendix C establishes the necessity of a hypothesis in [Theorem 3.1](../../../manuscript/latex/sections/03-sections-and-inseparability.tex#L21). Its example is no premise of that theorem or of the incompleteness theorem. |
| [C, opening and construction](../../../manuscript/latex/appendices/c-section-lifting.tex#L4) | A source morphism has a domain c.e. relative to the halting set and an ordinary partial recursive extension for its values. | An opening sentence about the output tag gives a reason for the two computability conditions before their definitions. |
| [C.1 and proof of the Turing property](../../../manuscript/latex/appendices/c-section-lifting.tex#L45) | The statement gives separation and failure of a common upper bound. The proof constructs the category, ranges, evaluator and total parameter. | State which target maps have no lift. A reader scanning the numbered statement otherwise sees a consequence of failed lifting and must infer the nonlifting assertion. |
| [Diagonal and separator](../../../manuscript/latex/appendices/c-section-lifting.tex#L133), [two nonlifting arguments](../../../manuscript/latex/appendices/c-section-lifting.tex#L170) and [upper bound](../../../manuscript/latex/appendices/c-section-lifting.tex#L198) | The parity set separates the diagonal domains. The unique section of the restricted codiagonal has nonrecursive output tag. Arbitrary target conditionals with the same summand inverse images have the same tag. A common upper bound for the two specified morphisms would equal that section. | Retain both nonlifting arguments. Uniqueness is a statement about sections of a specified partial injection. Theorem 3.1 prescribes only the two summand inverse images. |
| [Historical conclusion](../../../manuscript/latex/appendices/c-section-lifting.tex#L206) and [Appendix E](../../../manuscript/latex/appendices/e-reading-lean-proofs.tex#L129) | C checks the older theorem's target assumptions and weak Turing equation, then refers to an index “for the section.” The 2006 proof asks for an index of its composite with the inverse of the coding isomorphism. E explains the tag argument beside its proof-source link. | Announce the historical consequence at the opening. Retain its verification at the end, after the witness is available. |

## Proposed wording

1. Following the first sentence of Appendix C, insert:

   > The construction gives a nonrecursive set $A\subseteq\mathbb N$ such that the partial identities on $A$ and its complement belong to the source. In the category of partial functions a section sends $n$ to the right summand on $A$ and to the left summand on its complement. Every total source morphism is recursive in the chosen codings, so reading the summand of a lift would decide $A$. The same example disproves \cite[Theorem~4.1]{Lengyel2006} as stated.

   The final paragraph can then begin “The target $\Pfn$ is split” and proceed to the published hypotheses. Specify the type of the morphism being indexed in the last sentence as in item 3 below. [Historical source comparison](../V80_ASSERTIONS/primaryce.md)

2. In Proposition C.1, complete the sentence beginning “There are a Turing morphism” by replacing “are separated by complementary restriction idempotents in $\mathcal C_K$” with the following passage:

   > are separated by the partial identities on $A$ and $A^c$ for some nonrecursive set $A\subseteq\N$. Both partial identities belong to $\mathcal C_K$, with $D_{a_0}\subseteq A$ and $D_{a_1}\subseteq A^c$. There exists a partial function $s:\N\rightharpoonup\N+\N$ with $s^{-1}(i_0(\N))=A^c$ and $s^{-1}(i_1(\N))=A$. No such $s$ is the image under $F$ of a source morphism.

   Here $F$ is the inclusion and its coproduct comparison is the identity. Keep the sentence on common upper bounds. The displayed section in the proof witnesses existence. For any such $s$, its summand inverse images cover $\mathbb N$, and $\operatorname{tag}\circ s=\mathbf{1}_A$. The checked source distinguishes the [particular section](../../../Lean/CategoricalEssentialIncompleteness/OracleMissingLift.lean#L89) from the [arbitrary conditional](../../../Lean/CategoricalEssentialIncompleteness/V46MachineOracleTuring.lean#L154).

3. Replace the last three lines beginning “The earlier argument” with:

   > The earlier argument \cite[p.~11]{Lengyel2006} chooses a Turing index for the composite of the section with the inverse of the coding isomorphism. Here that composite is $F(b)^{-1}s_A:\N\to\N$ in $\Pfn$. A source morphism $u:\N\rightharpoonup\N$ with $F(u)=F(b)^{-1}s_A$ would give the lift $\ell=bu:\N\rightharpoonup\N+\N$, since $F(bu)=s_A$.

   The codomain of $s_A$ is a coproduct. The endomorphism whose index is sought has codomain $\mathbb N$. The two composites above are typed as written because the coproduct comparison is the identity for this inclusion. [Last paragraph](../../../manuscript/latex/appendices/c-section-lifting.tex#L219) · [2006 text, p. 11, as checked against the author's TeX, lines 894–910](../V80_ASSERTIONS/primaryce.md)

## Definitions, notation and scope

The types of the ordinary and oracle indices are fixed before use. For every oracle $B$ and indices $e,z,x$, $x\in W_{s(e,z)}^B$ iff $\langle z,x\rangle\in W_e^B$. This equation states exactly what parameter specialization means. The domain index $c$ of the given morphism and the diagonal morphism $d=\tau_K\Delta_{\mathbb N}$ have different names. The proof also distinguishes $D_{a_0}\subseteq A$ from equality, and specifies the opposite order $A^c,A$ for the two summand inverse images of the conditional. [Specialization](../../../manuscript/latex/appendices/c-section-lifting.tex#L102) · [Separator](../../../manuscript/latex/appendices/c-section-lifting.tex#L138) · [Order of summands](../../../manuscript/latex/appendices/c-section-lifting.tex#L186)

The opening and statement recommendations apply Knuth, Larrabee and Roberts, §1, items 5, 12–13, and Herb Wilf's discussion of what a reader learns from scanning theorem statements in §27, printed p. 59. The writing review covers all of Appendix C and its forward and backward references in the v83 source at `db33fca214084e37846e70c98d61e024331b5c16`. The [referee review](REFEREE.md) compares the historical claim with the author’s 2006 TeX and gives the scope of the Lean evidence. [Mathematical Writing, Stanford report](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf) · [2006 report record](https://academicworks.cuny.edu/gc_cs_tr/277/)
