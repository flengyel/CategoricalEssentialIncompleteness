# Receipt entries for the proof comparisons

The WSL2 verification tested `486414918381caf47688b1ae6574f1d9fe6e7b3a`. The manuscript read in this comparison is v81 at `986dee4d54d202a452009146cc29d19a544b0000`. For each declaration below, the v81 source file has both the Git blob ID and the SHA-256 content digest recorded in the v78 receipt. Each listed declaration has an entry in the current axiom audit. The strict elaboration column refers to the command on that file in the receipt. These checks apply to the existing declarations, not to the proposed applications in this report. [Pinned receipt](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/c37ff1685f9d67cc37fd8b3a7e1e3fe56011273f/docs/V78_WSL2_LEAN_VERIFICATION.json.gz)

The declarations below have prefix `CategoricalEssentialIncompleteness.V46.`. The right column gives the entire reported transitive axiom set.

| Declaration and source | Strict file elaboration exit code | Reported axioms |
|---|---:|---|
| [`PartialMaps.pullbackFactorIso`](../../../Lean/CategoricalEssentialIncompleteness/V46PartialMaps.lean#L87) | 0 | `Classical.choice`, `Quot.sound`, `propext` |
| [`PartialMaps.ofTotal_totalValue`](../../../Lean/CategoricalEssentialIncompleteness/V46PartialMapTotals.lean#L61) | 0 | `Classical.choice`, `Quot.sound`, `propext` |
| [`PartialMaps.totalValue_ofTotal`](../../../Lean/CategoricalEssentialIncompleteness/V46PartialMapTotals.lean#L69) | 0 | `Classical.choice`, `Quot.sound`, `propext` |
| [`RulePresentation.least_theorem_subobject`](../../../Lean/CategoricalEssentialIncompleteness/V46Inference.lean#L247) | 0 | `Classical.choice`, `Quot.sound`, `propext` |
| [`FiniteSigmaOne.finite_membership_PA`](../../../Lean/CategoricalEssentialIncompleteness/V46FiniteSigmaOne.lean#L171) | 0 | `Classical.choice`, `Quot.sound`, `propext` |
| [`SyntacticFiniteDerivations.standard_iff`](../../../Lean/CategoricalEssentialIncompleteness/V46SyntacticFiniteDerivationsStandard.lean#L53) | 0 | `Classical.choice`, `Quot.sound`, `propext` |
| [`SyntacticGeneratedAxioms.literalTheoremCarrier_model`](../../../Lean/CategoricalEssentialIncompleteness/V46SyntacticGeneratedAxioms.lean#L89) | 0 | `Classical.choice`, `Quot.sound`, `propext` |
| [`NamedArithmeticDiagonalBounds.semantic_bounds`](../../../Lean/CategoricalEssentialIncompleteness/V46NamedArithmeticDiagonalBoundsPrinted.lean#L58) | 0 | `Classical.choice`, `Quot.sound`, `propext` |
| [`UniformTrace.output_unique`](../../../Lean/CategoricalEssentialIncompleteness/V46UniformTrace.lean#L36) | 0 | `Classical.choice`, `Quot.sound`, `propext` |
| [`SyntacticSearch.search_uniform_of_functional`](../../../Lean/CategoricalEssentialIncompleteness/V46SyntacticSearch.lean#L94) | 0 | `Classical.choice`, `Quot.sound`, `propext` |
| [`UniformTrace.specialize_eval`](../../../Lean/CategoricalEssentialIncompleteness/V46UniformTraceBuilders.lean#L162) | 0 | `Classical.choice`, `Quot.sound`, `propext` |
| [`UniformTrace.specialize_natCast`](../../../Lean/CategoricalEssentialIncompleteness/V46UniformTraceComparison.lean#L48) | 0 | `Classical.choice`, `Quot.sound`, `propext` |
| [`Miller.Cut.Series.weight_tail`](../../../Lean/CategoricalEssentialIncompleteness/V46MillerCutSeries.lean#L45) | 0 | `Classical.choice`, `Quot.sound`, `propext` |
| [`Miller.Cut.Series.value_continuous`](../../../Lean/CategoricalEssentialIncompleteness/V46MillerCutSeries.lean#L89) | 0 | `Classical.choice`, `Quot.sound`, `propext` |
| [`Miller.Cut.Distance.boxDistance_le_productDistance`](../../../Lean/CategoricalEssentialIncompleteness/V46MillerCutBoxDistance.lean#L192) | 0 | `Classical.choice`, `Quot.sound`, `propext` |
| [`DecidableVariables.test_true_iff`](../../../Lean/CategoricalEssentialIncompleteness/V46CategoricalListLaws.lean#L251) | 0 | `Classical.choice`, `Quot.sound`, `propext` |

The receipt contains 1,975 successful verifier commands and 42 successful targeted commands. All 16 dependency worktrees are clean at their pins before and after verification. The receipt records 32,018 current and 1,274 retained declarations. Its SHA-256 is `5cfcb98111e2e0653da027ba008013c44876c628165cd028c873c33d2fd4b5bc`. The v81 manuscript-source, archive, PDF and correspondence checks and six axiom-parser tests ran separately. A WSL2 run on the v81 inputs is outstanding.
