# Formalization review and v48 abstract revision — 7 November 2026

The inspected formalization supports the reported completion of Proposition 7.5 and Theorem 7.6. The next task is Proposition 7.8: numerical syntax and finite-derivation initiality, together with the stated comparisons to named arithmetic syntax and proof coding. No discrepancy warranting reversal of the inspected completion claims was found.

Reviewed main: `c51c34d37df83ee9c568b7fe0ed92a801a3215c4`. The review read `FORMALIZATION_STATUS_V47.md`, the corresponding manuscript sections, the recent arithmetic proof chains, numerical and cosheaf infrastructure, and the committed verification evidence. The new `FORMALIZATION_STATUS_V48.md` retains the same result statuses.

## Manuscript change

Version 48 installs the abstract retained in the approved front-matter report. The introduction and the other mathematical source files are unchanged. Of 22 TeX files, only `abstract.tex` and the version/date metadata in `preamble.tex` differ from reviewed main. The PDF, source archive, current manifest, correspondence file, and current instructions advance together to v48.

This changes the verification target without changing a Lean statement or proof. The archive preserves earlier manuscript versions. The `V46` module prefix continues to name the existing implementation.

## Recent arithmetic results

Lean paths below are relative to `Lean/CategoricalEssentialIncompleteness/`; declaration prefixes are abbreviated.

| Claim | Source evidence | Assessment |
|---|---|---|
| Numeral fibers have the required initial algebra | `V46ArithmeticIndexedFibers.lean`: `algebraEquivalence`, `fiberInitial`, `individualFiberAlgebraIso`; `V46ArithmeticIndexedFibersPresentation.lean`: `individual_oldGamma_comparison`, `individual_oldGamma_model` | Actual categorical initiality and algebra comparison. The universal property is not replaced by a chosen evaluator. |
| The printed family is the constructed family | `V46ArithmeticIndexedPrintedFamily.lean`: exponential coefficient comparison, realized square, printed conclusion realization; `V46ArithmeticIndexedProvabilityFibers.lean`: `printedProvability_numeral` | The coefficient, conclusion, and numeral-fiber comparisons are proved. The provability comparison covers internal sentence codes in every PA model for an external numeral index. |
| One morphism selects independent sentences uniformly | `V46ArithmeticUniformSearch.lean`, `V46ParameterizedTuringDiagonal.lean`, `V46ArithmeticUniformSentence.lean`, `V46ArithmeticUniformIndependent.lean` | A joint partial morphism is constructed before the Turing factor supplies one total source morphism. The final existential precedes the index and consistency premise. |
| The final theorem concerns the stated extension | `V46ArithmeticIndexedPAEnumeration.lean` and the final native-proof/code comparisons in `V46ArithmeticUniformIndependent.lean` | The extension uses the actual sentence-guarded PA axiom/trace enumeration and native positive and negative proofs. The final independence theorem concerns external natural indices, not arbitrary nonstandard indices. |

The reviewed strict statement checks expand the relevant definitions. The final arithmetic conclusions do not add an unproved correctness or admissibility field. Preserve these completed results; reopen a row only for a demonstrated mismatch.

## Remaining work

The correspondence table has 62 numbered results and three numbered definitions. Ten numbered results remain pending: 7.8, 8.1–8.6, 9.3, 9.4, and 9.6. These are remaining Lean correspondence obligations. The manuscript contains arguments for them.

Definition A.2 already has the generic occurrence-list fold, sentence pullback, monic inclusion, and negation restriction. Its pending status concerns identification with the concrete sentence-code predicates in each application.

| Priority | Required endpoint | Existing work to retain |
|---|---|---|
| 1: Proposition 7.8 | Numerical syntax and typed finite-derivation initiality in all stated parameter slices; literal syntax, substitution, proof, and conclusion-image comparisons | Numerical equivalence, stable lists for every coefficient/parameter object, decidable variables, transported syntax initiality, generic successful-tree/inference comparison, and generated-theory theorem |
| 2: Proposition 9.3, then 9.4/9.6 | Initiality of the actual typed H-algebra in E/S; identify its conclusion range and endpoints with the existing presentations | Fork syntax initiality, coded proof object, conclusion-range leastness and consistency, and the arbitrary c.e.-axiom endpoint-extension theorem |
| 3: Miller 8.1–8.6 | A single oracle program with representation-independent domain and values; then the category, cut reduction, syntax/proofs, and application | General categorical machinery; fixed-oracle approximation results do not prove representation independence |

For 7.8, the numerical equivalence and generic inference construction provide a short categorical route. The substantive remaining comparison is with the literal named syntax and proof codes. A bijection of carriers does not establish the constructor, substitution, or derivability diagrams. The first batch should finish these comparisons instead of introducing another abstract layer.

For 9.3, folds must accept target operations whose recursive realizers are total only on their carriers. The existing proof-tree recursion theorem's globally total and inhabited-target assumptions are too strong for this universal property. This is a constraint on the next construction, not a defect in an existing claim of completed 9.3: that row is already pending.

The numerical batch and the subsequent cosheaf batch are specified in [the Codex continuation instructions](../CODEX_CEI_V48_NUMERICAL_2026-11-07.md).

## Verification evidence

The committed record `docs/V46_SYNTAX_CONTINUATION_VERIFICATION_2026-11-05.json`, under `final.verifier`, records:

- Proof commit `ff0363b8ec2fdad87cbdc3b3c53d8d0f614fd71f`; run `.codex-work/verify-20261107T033748Z-uOYuIx`.
- 965 commands, all exit zero; 1,274 retained and 13,290 current production declarations.
- 497 current production modules, matching the reviewed main-tree inventory.
- 1,247 recorded input hashes; recomputed snapshot digest `1501719b0ea7367bc54a95a5aeadb5a0160a074e521a2619f276ba2c37f059e9`.
- Axiom union exactly `propext`, `Quot.sound`, and `Classical.choice`.
- Sixteen dependency worktrees pinned and clean at the recorded start/end; 356 imported-source pin checks.
- `whole_current_manuscript_complete = false`.

The proof commit and reviewed main differ only in five report files, none in the recorded verification inputs. The review checked the module inventory, input-path inventory, snapshot digest, audit/verifier implementation, selected source hashes, and the source/report commit comparison. This was source and evidence review; no new Lean kernel run was performed.

For v48, `latexmk` succeeded, producing a 73-page PDF. The final TeX log has no undefined references/citations, warnings, overfull/underfull boxes, or missing characters. Pages 1–2 were rendered and visually checked. `python3 scripts/verify.py --manuscript-only` passed the 22-file source, 25-entry manifest, source-archive, PDF-copy, and correspondence checks.

The associated [editorial verification record](../V48_ABSTRACT_VERIFICATION_2026-11-07.json) records this scope separately from the earlier full Lean verification.
