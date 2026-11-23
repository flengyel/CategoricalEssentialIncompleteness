# Correspondence for the abstract, §§1–10 and Appendices A–E

The LaTeX source examined is [d80a23b07406dc0e44b010a7d78f2318980b6046](https://github.com/flengyel/CategoricalEssentialIncompleteness/tree/d80a23b07406dc0e44b010a7d78f2318980b6046/manuscript/latex), edition 80. The initial statement reconstructions precede the comparison with the Lean declarations. The entries below give the hypotheses, conclusions, dependencies and corresponding proof locations or identify the missing inference. A source interval can contain several assertions. The 77 numbered results comprise 18 theorems, 19 lemmas, 27 propositions and 13 corollaries. There are also three numbered definitions and 77 proof environments. [Numbered-environment comparison](numbered-coverage.md) · [Unnumbered passages](unnumbered-coverage.md) · [39 cited works and all 78 citation-key occurrences](citation-index.md)

| Printed passage | Comparison |
|---|---|
| Abstract, §1, §2, §3 | [Theories, restriction categories and the diagonal comparison](01-introduction-and-comparison.md) |
| §4, §5 | [Internal theories, the two adjunctions and partial-map slices](04-theories-and-slices.md) |
| §6, §7 | [Syntactic categories, named syntax and model interpretation](06-syntax-and-models.md) |
| §8, including its four nested TeX inputs | [Arithmetic, its interpretation and uniformity](08-arithmetic.md) |
| §9, §10 | [Miller sequences and the three-point space](09-miller-and-cosheaves.md) |
| Appendix A | [Syntax, substitutions and deductive closure](04-theories-and-slices.md#appendix-a-syntax-substitution-and-deductions) |
| Appendix B | [Effective cosheaves and the fork](09-miller-and-cosheaves.md#appendix-b--appendicesb-three-point-cosheavestex) |
| Appendix C | [The oracle-restricted counterexample and necessity of section lifting](appendices-c-e.md#c-necessity-of-section-lifting) |
| Appendix D | [A faithful family of model interpretations](06-syntax-and-models.md#appendix-d) |
| Appendix E | [Two proof readings and their pinned declarations](appendices-c-e.md#e-reading-the-lean-proofs) |

[Verification of primary sources](primary-sources.md) · [Arithmetic and model interpretations](primary6.md) · [Uniformity in §8](primary8.md) · [Miller sequences and cosheaves](primary9.md) · [The section in the 2006 proof](primaryce.md) · [Derivations of Miller existence and failure of source local connectedness](external-proofs.md)

## Counts at the reviewed source

| Class | Findings established in this correspondence |
|---|---|
| Mathematical errors | 0 counterexamples to a printed mathematical conclusion established |
| Ambiguities | 1 passage counted in Appendix C, lines 108–113. The informal description leaves the two arguments of the parameter function implicit. Edition 81 specifies the function, its inputs, its independence of the oracle, and its defining equality of domains. |
| Lean omissions | At least 6 conclusions lack an identified proof at the printed types, enumerated below. Additional application-level comparisons remain open. |
| Proof gaps | 0 gaps established in the mathematical arguments of the manuscript, with the cited theorems available as mathematical premises |

These are counts of findings established so far. The outstanding exact-type comparisons prevent a final count of Lean omissions. The consecutive-clean count is **0 of 2**. The last complete WSL2 replay tested manuscript v78 at `486414918381caf47688b1ae6574f1d9fe6e7b3a`. Its receipt records 1,975 verifier commands and 42 targeted commands, 16 dependency pins, and axiom results for 32,018 current and 1,274 retained declarations. The audit matched all 2,618 recorded input digests to that commit. The v80 and v78 Lean trees both have Git tree ID `665314f89e26c9850c9852114285c22135e4f9da`. A v80-specific kernel receipt is absent. [v80 correspondence](../../../FORMALIZATION_STATUS_V80.md) · [Source-pinned WSL2 report](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/c37ff1685f9d67cc37fd8b3a7e1e3fe56011273f/docs/V78_WSL2_LEAN_VERIFICATION.md) · [Successful pinned verification and axiom receipt](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/c37ff1685f9d67cc37fd8b3a7e1e3fe56011273f/docs/V78_WSL2_LEAN_VERIFICATION.json.gz)

## Six conclusions without an identified Lean proof at the printed types

1. **§6.** For the target whose objects are the recursively generated sets of §6, realization on objects and the identity on program representatives induce a fully faithful, essentially surjective functor. The target of the located Lean equivalence still has object terms.
2. **§8.6.** For each consistent c.e. extension of PA in the fixed language, the supports of the printed numeral instances of the formula $\alpha$ are the two specified pullbacks. The identity on indices sends both supports into the corresponding supports for each extension. This action defines the printed functor. A checked functor in a different syntax would suffice together with these identifications and their naturality.
3. **§8.6, Bernardi.** For each precomplete equivalence relation on the natural numbers, two distinct classes are recursively inseparable. The same conclusion for disjoint nonempty unions follows by choosing one class on each side. Counted here as one omission.
4. **§8.6, Bernardi's PA example.** The relation on program indices given by PA-provable universal equivalence of their graphs is precomplete. For every partial recursive $g$, produce total recursive $h$ such that $g(n)\downarrow=j$ implies PA proves the universal graph equivalence of programs $h(n)$ and $j$. This requires the program totalization and the PA proof for each convergent standard trace.
5. **§9.** There exists $a\in[0,1]^{\mathbb N}$ such that if the same index $d$ computes $r$ from every name of $a$ with the specified error bounds, then $a(d)=r$. The located Lean incompleteness theorem takes the hypothesis that $a$ has this property.
6. **Appendix D.** For every consistent c.e. $T\supseteq\mathrm{PA}$, the connected restriction idempotents on the natural-number object of the unprimed syntactic recursion category fail to distinguish all parallel endomorphisms. More precisely, in each such category there are distinct endomorphisms of $\omega$ agreeing after every connected restriction idempotent on $\omega$. Joint faithfulness of a family of interpretations into locally connected categories does not imply local connectedness of the source.

## Other exact comparisons

The following instances each require either a proof at the displayed type or an application of an existing declaration. The detailed rows also distinguish categorical equivalence from an isomorphism at a common object set, and identify mathematical assertions used only in comparisons with the literature.

| Passage | First inference requiring a matching proof |
|---|---|
| §3, summand idempotents | In the generality of the stand-alone observation, every upper bound fixes both coproduct injections, hence their copairing. The stronger hypotheses of the subsequent numbered application already give its instance. |
| §5, unit over an arbitrary object | Given $i:S\hookrightarrow Y$ and $q:Q\to Y$, the unit at $q$ is total iff the projection $Q\times_Y S\to Q$ is invertible iff $q$ factors through $i$. A factorization gives a section of that monic projection. |
| Lemma 6.4 | For the supplied selector graph $L$, construct the finite disjunction of $L(x,\bar j)\wedge D_j(x)$ and apply finite membership to this formula in each PA model. Programs which both return bits and compute the same standard function can have different graphs in a nonstandard PA model. [Counterexample](06-syntax-and-models.md#selector-reconciliation-and-consequences) |
| §9 and §10 | Identify the topology of the weighted Hilbert-cube metric with the product topology. For the three-point space identify the opens of the glued Sierpiński subspaces. In each endpoint theory extract an index outside the union of its two signed **atomic** supports: coverage by disjoint c.e. supports would decide either support and separate the diagonal pair. |
| Appendix A, propositional calculus | In a regular category with finite coproducts and the specified initial algebra, form the three axiom schemes, nullary axioms and binary modus ponens. For the unary rule whose premise and conclusion are the unique $0\to S$, the second pullback projection gives closure over any $q:Q\to S$. The identified Lean instance instead uses strict initiality under finitary extensivity. |
| Proposition B.10 | From a putative total equality classifier $V\times V\to1+1$ whose true fiber is the categorical diagonal, evaluation at vertices must classify equality there. Singleton probes witness each diagonal and off-diagonal test. Apply the already checked obstruction for componentwise equality decisions. |

The [WSL2 handoff](../../CODEX_WSL2_CEI_V80_LEAN_HANDOFF.md) gives the required statement and axiom checks. The proof sources and the receipt for a full replay on the revised inputs remain outstanding.
