# Independent readings of manuscript v81 at 830d03a

Both readers reconstructed the paper from its 25 TeX inputs before seeing the correspondence or consulting the Lean proofs. They recorded all 667 passages, including the 77 numbered results and three numbered definitions. Each reader sealed a source verdict before the two compared their findings. [Tested proof commit](https://github.com/flengyel/CategoricalEssentialIncompleteness/commit/830d03a5adcf144a003feb36f88bd06e0c5b0cf5) · [Verification report](../../../V81_WSL2_LEAN_VERIFICATION_830d03a.md) · [Machine-readable receipt for this commit](../../../V81_WSL2_LEAN_VERIFICATION_830d03a.json.gz)

| Evidence | First reader | Second reader |
|---|---|---|
| Manuscript reconstruction | [Typed assertions](first/reconstruction.md) | [Typed assertions](second/reconstruction.md) |
| Independent source comparison | [Verdict](first/source-verdict.md) | [Verdict](second/source-verdict.md) |
| Comparison after both verdicts were sealed | [Findings](first/reconciliation.md) | [Findings](second/reconciliation.md) |
| Separate Lean checks | [Statements and proof applications](first/replay-notes.md) | [Twenty-four strict checks](second/kernel-supplement.md) |
| Comparison with the completed run | [Official transcript check](first/receipt-confirmation.md) | [Receipt and source hashes](second/receipt-confirmation.json) |

The readers found checked counterparts for every numbered item. Across the full text they identified one false unrestricted historical implication, one ambiguity and fifteen positive literature claims without a checked proof at the cited types. These amount to sixteen proof gaps when the invalid implication is included. No numbered result depends on those fifteen claims or on that implication. The readers could not confirm the original numbering of Cockett’s list-recursion references from a copy of the 1990 article. The two original source verdicts preserve each reader’s own grouping of findings.

An earlier invocation at this same commit recorded 2,038 successful subprocesses before interruption. The complete replay has its own transcript and receipt. [Interruption record](interrupted/interruption.json) · [Original partial verifier output](interrupted/official-partial.json.gz)

The later proof commit adds the categorical Di Paola–Heller comparison with a nonzero identity, the two Bernardi theorems, Montagna’s productive morphism and four background results in Appendix A. Its proofs and its two independent readings use a separate receipt. [Later v81 report](../../../V81_WSL2_LEAN_VERIFICATION.md)
