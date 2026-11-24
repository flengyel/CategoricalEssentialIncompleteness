# First reader’s reconciliation for manuscript v81

I compared our two independent verdicts after both were sealed. At source commit `6775f0b3a5fb668f9390b21440f3f6c57bc65930`, we agree on the proof coverage of all 77 numbered results and three definitions, on the six missing historical theorems, on one false historical assertion, on one ambiguous passage and on one incorrect page reference. The whole paper has zero qualifying clean reports. [Tested sources][tested] · [Active whole-paper correspondence][correspondence] · [WSL verification report][verification] · [Canonical receipt][canonical] · [Commit-specific kernel receipt][permanent]

| Scope at the tested revision | Count |
|---|---:|
| Mathematical errors | 1 |
| Ambiguities | 1 |
| Positive historical conclusions without a checked proof at their published types | 6 |
| Proof gaps in the 77 numbered arguments or their mathematical premises | 0 |
| Proof gaps when the six missing proofs and the invalid historical inference are both counted | 7 |
| Additional incorrect primary-source locators | 1 |

The second reader counts six proof obligations for true historical conclusions and reports the false historical assertion as a mathematical error. My broader column counts the invalid inference in that assertion once more as a proof defect. The six formal obligations and the one false assertion agree item for item. In §1 the restricted Di Paola–Heller conclusion requires a nonzero identity on the Turing object. In §8.3 the unqualified sentence about effective extensibility admits a reading contradicted by a complete consistent theory. Di Paola and Heller’s item (3) in §8.1 is on p. 595. The six missing conclusions belong to Heller 9.2, Lengyel 21 and 26, van Dijk–Gietelink Oldenziel 5.19 and 5.20, and Bauer–Hanson 6.4. None supplies a premise of a numbered result. Each reader also checked both directions of the Cockett–Hofstra representation theorem. [Historical statements and mathematical dependencies][literature]

## The 80 numbered rows

The active Lean-declarations column contains **855 individually named occurrences, 852 distinct names and 11 further module references**. My independent report used the linked historical declaration table when it described 844 names as the numbered correspondence. I correct that description here. The active rows at `6775f0b` are byte-for-byte identical to the active rows at `98f8d0d`, including their 852 names. I checked every raw cell against its earlier Git blob, resolved every printed reference in order and checked the defining source location and Lean type for all 852. [Direct names only, one record per printed item](active-numbered.tsv.gz) · [All 80 comparisons and defining source locations](numbered-reconciliation.json.gz) · [Earlier 852-name register][prior] · [Historical 844-name table][historic]

The historical table has 847 individually named occurrences and 844 distinct names. It shares 836 distinct names with the active table. The only differing rows are Proposition 10.1 and Theorem B.7. The older declarations are in `CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork`. All of the replacements are in `CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation`. The namespace matters for `evaluation_product` and `tau_isTuring`, whose local names occur in both implementations. [Proposition 10.1][tenone] · [Theorem B.7][bseven]

| Row | Historical names no longer individually listed | Current individually listed names |
|---|---|---|
| 10.1 | `evaluationRangeFunctor`, `evaluation_product`, `evaluation_sup`, `left_evaluation_turing`, `right_evaluation_turing` | `evaluation_span`, `evaluation_restriction`, `evaluation_range`, `evaluation_zero`, `evaluation_finset`, `evaluation_product`, `evaluatedSumColimit`, `left_isTuring`, `right_isTuring` |
| B.7 | `central_specialized`, `tau_isTuring`, `tau_parameterization` | `tau_isTuring`, `left_graph`, `right_graph`, `component_fibre`, `center_tuple_graph`, `forkParameter_total`, `fork_parameterizes` |

The substitutions retire eight names and add sixteen. They supply the evaluator of the tuple diagram, its partial graphs at the centre and endpoints, its total parameter, and the equations for the preservation claims. Both readers’ independently reconstructed types require these concrete morphisms.

The second reader’s register contains 1,078 distinct names. Its additional 226 declarations come from expanding the eleven module references. Among the 301 distinct declarations obtained by opening those modules, 75 already occur explicitly in their rows. Every extra declaration in the second register has a particular module reference in the machine-readable comparison. The other 76 rows contain only the directly named declarations. [Row-by-row direct and supporting sets](numbered-reconciliation.json.gz)

| Row | Direct names | Module references | Distinct names from the modules | Already direct | Further supporting names |
|---|---:|---:|---:|---:|---:|
| 6.9 | 9 | 1 | 21 | 0 | 21 |
| 10.7 | 65 | 8 | 227 | 65 | 162 |
| 10.8 | 10 | 1 | 34 | 10 | 24 |
| D.1 | 4 | 1 | 19 | 0 | 19 |
| Total across these four rows | 88 | 11 | 301 | 75 | 226 |

## Kernel checks and signatures

I compiled six further independent probe files under the pinned Lean 4.35.0-rc2, one worker per process. They printed the full type and transitive axiom list of **1,657 distinct declarations**. This union includes every active, historical and module-expanded numbered name, my 591 supplementary statements and the second reader’s 45 named historical statements. A name can serve in several groups. The six exits were zero. Every reported axiom set agreed with the originating records and was a subset of `Classical.choice`, `propext` and `Quot.sound`. [Per-name axiom manifest for the full union](named-probes.json.gz) · [Lean inputs, output and command receipts](reconciliation-probes.zip) · [Detached checked counts](local-confirmation.json)

At the reconciliation seal, the official full replay was pending. The detached checker validates the physical rows and their names against immutable Git blobs, checks every axiom record against the corresponding raw reader output, and can then validate the completed WSL receipt. In receipt mode it verifies the official source snapshot, both axiom audits, dependency state, command exits, and output digests. It reports the overlap of each named set with the official current, retained and supplementary statements. The option to check the bound reader manifest verifies all 1,657 names including supporting names outside the official audit scopes. [Detached checker](confirm-reconciliation.py) · [WSL verification report][verification] · [Canonical receipt][canonical] · [Commit-specific receipt][permanent]

Run the source-and-reader check from this directory with `python3 confirm-reconciliation.py --repo /path/to/repository`. To confirm the published full result, add `--receipt /path/to/docs/V81_WSL2_LEAN_VERIFICATION_6775f0b.json.gz --canonical /path/to/docs/V81_WSL2_LEAN_VERIFICATION.json.gz --require-bound-reader-manifest`. Optional raw verifier and command-log paths provide byte-for-byte comparison with the original outputs. The canonical alias check applies while the canonical receipt targets this same revision. The commit-specific receipt can be checked on its own in later revisions.

I sign this reconciliation as the independent first reader. The original first verdict has SHA-256 `6796348976e4ab96dbaf3c1f72d3a8c65bfc097c974850d7042fbd521f9ab0bf` and its independent seal has SHA-256 `f5a7692e8dccdbf8b5e7d79d29e876edd451e58a91a95cee48e69b7f579a7589`. The second verdict has SHA-256 `0a7df0583816eed431c598fce8149bc1b477ec3d126471f4951ae7d78023d101` and its checksum manifest has SHA-256 `4f8e7db38995bfdefb9dab7962aa591219b19f3ed69b9e2c7031949b69fbd0e1`. Both original seals verified before reconciliation. [Reconciliation signature and artifact digests](signature.json)

[tested]: https://github.com/flengyel/CategoricalEssentialIncompleteness/tree/6775f0b3a5fb668f9390b21440f3f6c57bc65930
[correspondence]: https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/6775f0b3a5fb668f9390b21440f3f6c57bc65930/FORMALIZATION_STATUS_V81.md#numbered-statements
[verification]: https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/main/docs/V81_WSL2_LEAN_VERIFICATION.md
[canonical]: https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/main/docs/V81_WSL2_LEAN_VERIFICATION.json.gz
[permanent]: https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/main/docs/V81_WSL2_LEAN_VERIFICATION_6775f0b.json.gz
[literature]: https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/6775f0b3a5fb668f9390b21440f3f6c57bc65930/docs/reviews/V81_WSL2_ASSERTIONS/historical-comparisons.md
[prior]: https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/6775f0b3a5fb668f9390b21440f3f6c57bc65930/docs/reviews/V81_WSL2_AUDITS/tested-98f8d0d/first/numbered-declarations.tsv
[historic]: https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/6775f0b3a5fb668f9390b21440f3f6c57bc65930/docs/reviews/V81_PROOF_COMPARISONS/numbered-receipt.md
[tenone]: https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/6775f0b3a5fb668f9390b21440f3f6c57bc65930/FORMALIZATION_STATUS_V81.md#L249
[bseven]: https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/6775f0b3a5fb668f9390b21440f3f6c57bc65930/FORMALIZATION_STATUS_V81.md#L282
