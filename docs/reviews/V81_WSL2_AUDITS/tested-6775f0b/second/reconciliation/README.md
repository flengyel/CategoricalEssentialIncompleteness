# Reconciliation of the second reading with the first

At `6775f0b3a5fb668f9390b21440f3f6c57bc65930`, the numbered correspondence explicitly names **852 distinct Lean declarations in 366 defining modules**. Its 80 rows contain 855 declaration mentions and 11 references to modules or collections. Three names occur in two rows. The 77 printed results and three definitions agree in both readings. This reconciliation was written after the two reports were sealed. Their original digests are recorded in the machine-readable comparison. [Tested numbered correspondence](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/6775f0b3a5fb668f9390b21440f3f6c57bc65930/FORMALIZATION_STATUS_V81.md#numbered-statements) · [Each literal token and its resolved declaration](named-core.json.gz) · [Counts, differences and original seals](reconciliation.json).

| Source of the count | Declaration mentions | Distinct declarations | Scope |
| --- | ---: | ---: | --- |
| First reader’s historical numbering crosswalk | 847 | 844 | The named list in the crosswalk on the original manuscript commit `986dee4`. The first reader checked the listed declarations at the current tested commit. |
| Current numbered table | 855 | 852 | Each backticked declaration in the column headed “Lean declarations.” Shorthand resolves to its actual fully qualified declaration. |
| Second reader’s expanded probe | 1,081 | 1,078 | The 852 current names plus 226 names resolved from the 11 references to whole modules or collections. |

The 78 unaffected rows retain the same ordered names. The remaining two rows changed at `2a5c1dd` when the formalization identified the evaluator on the numerical tuple diagram and the action of vertex evaluation on monic partial spans. The older code for an equivalent fork category also checks. The two rows now explicitly refer to the tuple diagram itself. The common set has 836 names. The update removes eight named entries and adds sixteen. [Tuple-diagram update](https://github.com/flengyel/CategoricalEssentialIncompleteness/commit/2a5c1dd1b9161570e377bddff566c899928d9370) · [Proposition 10.1](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/6775f0b3a5fb668f9390b21440f3f6c57bc65930/FORMALIZATION_STATUS_V81.md#L249) · [Theorem B.7](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/6775f0b3a5fb668f9390b21440f3f6c57bc65930/FORMALIZATION_STATUS_V81.md#L282).

| Row | Historical names in `LocalConnectedness.EffectiveFork` | Current names in `V46.ForkTupleEvaluation` |
| --- | --- | --- |
| Proposition 10.1 | `evaluationRangeFunctor`, `evaluation_product`, `evaluation_sup`, `left_evaluation_turing`, `right_evaluation_turing` | `evaluation_span`, `evaluation_restriction`, `evaluation_zero`, `evaluation_range`, `evaluation_product`, `evaluatedSumColimit`, `evaluation_finset`, `left_isTuring`, `right_isTuring` |
| Theorem B.7 | `tau_isTuring`, `tau_parameterization`, `central_specialized` | `tau_isTuring`, `left_graph`, `right_graph`, `center_tuple_graph`, `forkParameter_total`, `fork_parameterizes`, `component_fibre` |

All sixteen current names appeared in the second reader’s original kernel output. Eleven also appear individually in the first reader’s separate historical/application supplement. The other five occur in named proofs checked there. The proof of `Checks.endpoint_morphisms` applies `left_isTuring` and `right_isTuring`. The proof of `Checks.fork_parameter` applies `forkParameter_total`, `fork_parameterizes` and `component_fibre`. For all 847 current names individually probed in both readers’ material, the displayed types agree up to whitespace, the transitive axiom sets agree, and the defining source SHA-256 digests agree. [First reader’s relevant checks](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/6775f0b3a5fb668f9390b21440f3f6c57bc65930/Lean/CategoricalEssentialIncompleteness/V46ForkTupleTuringChecks.lean#L53) · [Machine comparison of both sealed mappings](sealed-comparison.json).

The 11 collection references occur in Theorem 6.9, Proposition 10.7, Proposition 10.8 and Theorem D.1. Expanding them adds 21, 162, 24 and 19 unique names, respectively. The expanded applications sometimes refer to the same declarations as other entries in the same collection. The counts above use the union. The three repeat mentions in the current explicit list are `ConcreteNamedComparison.plain_termSubstitution_value` and `ConcreteNamedComparison.plain_formulaSubstitution_result` in Proposition 6.7 and Lemma 7.5, and `EffectiveFork.totalEquivalence` in Propositions 10.2 and B.2. [Token-by-token ledger](named-core.json.gz).

## Proof-gap convention

Both readers identify six positive historical results that lack a checked proof at their original types. They are Heller 9.2, Lengyel 21 and 26, van Dijk and Gietelink Oldenziel 5.19 and 5.20, and Bauer and Hanson 6.4. Both readers separately identify the invalid inference in the unrestricted Di Paola–Heller 8.15 argument. Equality of zero and the identity does not yield a contradiction in the one-morphism category. The corrected form assumes a nonzero identity. Corollary 3.3 already supplies its nonzero hypothesis, and all numbered proofs remain accounted for. [Historical ledger and dependencies](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/6775f0b3a5fb668f9390b21440f3f6c57bc65930/docs/reviews/V81_WSL2_ASSERTIONS/historical-comparisons.md).

| Unit | Count |
| --- | ---: |
| Missing Lean proofs of positive historical conclusions | 6 |
| Invalid historical inference in the unqualified Di Paola–Heller statement | 1 |
| Whole-paper proof gaps counting both groups | 7 |
| Proof gaps in numbered arguments | 0 |
| Mathematical errors, ambiguities and additional locator errors | 1 each |
| Consecutive clean reports | 0 |

The second report’s count of six measures the missing positive kernel proofs. The first report’s count of seven also includes the false historical inference. The single ambiguity concerns the opening of §8.3, and the additional citation locator is Di Paola and Heller’s item (3) on page 595. The count of seven includes the one mathematical error in the proof-gap column. No additional mathematical finding arose from comparing the two reports. [Counts by convention](reconciliation.json).

## Reproduction

The validator reads the table and the 366 defining files from Git at the tested commit. It checks every numbered label, every token, every declaration source line and SHA-256 digest. In strict replay mode it emits an individual `#check` and `#print axioms` for all 852 current names. Three explicit applications test both endpoint evaluators, total specialization at each parameter fork and the equivalence between the specialized computation and the graph on each component. [Applications](Applications.lean) · [Lean command receipt](core-kernel.json) · [Raw kernel output](core-kernel.log.gz).

Run from this directory with a repository containing the tested commit.

```sh
python3 validate-core.py --checkout /path/to/repository --verify-log core-kernel.log.gz
python3 compare-sealed.py --first /path/to/first/report-directory --second /path/to/second/report-directory
```

A fresh replay uses a built checkout of the tested commit with the pinned dependencies.

```sh
python3 validate-core.py --checkout /path/to/tested-checkout --run-lean
```

The strict check validates the narrow numbered list and the three stated applications. The complete project command history, all production declarations and the retained axiom inventory belong to the [canonical per-commit receipt](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/main/docs/V81_WSL2_LEAN_VERIFICATION_6775f0b.json.gz).
