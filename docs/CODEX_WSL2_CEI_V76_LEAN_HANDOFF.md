# WSL2 Codex — Lean proofs and verification for manuscript v76

Work in `/home/flengyel/src/CategoricalEssentialIncompleteness`. Fetch `origin/main`, inspect the worktree and integrate the current main without discarding local work or a newer manuscript. The v76 manuscript commit is `e11906faf32720516d36f3bfd30a9d4ca278f3c9`. Check its ancestry and read [AGENTS.md](../AGENTS.md), the [active manifest](../MANUSCRIPT_CURRENT.json), and the [v76 correspondence](../FORMALIZATION_STATUS_V76.md). Complete the outstanding Lean proofs and comparisons, run the checks below, and **commit and push the tested changes and report to public `origin/main`**. No separate push approval is needed.

## Proofs and comparisons

1. Complete §§1–4 of the [earlier proof assignment](CODEX_WSL2_CEI_V74_PROOF_REPAIRS.md) against the active manuscript. This includes correcting the docstring for the partial inverse in Theorem 5.2, proving the §5 example for every infinite c.e. carrier, the Appendix D obstruction to the Turing property, and the example after Corollary 4.3 concerning global points in a category of group actions. Identify or prove the comparisons for the coded objects in §6 and the numerical observation functor in §8. Update the correspondence selected by the active manifest. For v76 this is `FORMALIZATION_STATUS_V76.md`; the older assignment's closing reference to the v74 ledger is historical.
2. Check the two §6.2 postfix implications at their stated domains. Constructor input consists of typed children. Parsing an accepted word gives its ordered children. In Appendix C, specialize the obstruction to **every** partial map with the two prescribed inverse images of the summand domains, allowing any values within each summand. Reuse the general obstruction if it proves that quantifier. Add the exact specialization and its statement check if needed. [Counterexample, proofs, and source declarations](reviews/V75_MATHEMATICAL_EXPOSITION.md)
3. Verify the v76 changes against their actual Lean declarations and independent statement checks. In Theorem 4.7 check the target presentation's initial derivation algebra for each axiom subobject, the sentence-inclusion square, and admissible substitution under a binder. In Theorem 5.3 check initiality for every parameter and axiom subobject, evaluation of an arbitrary closed slice extension, and the naturality square used to transport closure. In §8.2 use the presentation at the numeral for the index, and in Theorem 8.6 check the exclusion of finite derivations of both the output sentence and its negation. In Theorem 9.7 check the ordered-field axioms with the rational bounds, strict-order asymmetry, and the fixed-language, uniformly semidecidable extension hypothesis. Keep existing proofs when their types already establish the printed claims. [Proof comparisons and exact source references](reviews/V76_HYPOTHESES_AND_PROOF_COMPARISONS.md)

## Verification and delivery

Integrate any new declarations into the project imports and statement and transitive axiom audits. Run targeted strict checks on affected modules. Record their commands and exit codes. With the repository's pinned toolchain and dependencies, run the following from the repository root.

```bash
python3 scripts/test_verify_axiom_parser.py
python3 scripts/verify.py --manuscript-only
bash scripts/verify-wsl.sh
```

The manuscript-only check verifies the paper artifacts. The final command runs the full Lean verification serially under its build lock and records the result under `.codex-work/verify-*`. Commit the proof and correspondence inputs locally before the full run so its recorded starting SHA identifies the tested sources. If a fix changes a verification input, repeat the affected checks and the full run for the final candidate. Keep the existing permitted-axiom policy.

Record the result in `docs/V76_WSL2_LEAN_VERIFICATION.md`. For each item, give the paper location, Lean declaration and type, whether an existing proof sufficed or a new proof was needed, and the verification evidence. Distinguish targeted checks from the full replay. If a genuine blocker remains, identify the failed claim or command and its evidence, and report any independent work completed.

Push the proof commit and report to `origin/main` without force. Fetch again, verify the remote tip and active manuscript version, and compare the tested inputs with the fetched copies. Return the tested SHA, fetched main SHA, report link, and full-run result to the originating manuscript chat. A separate commit adding the report can have a different SHA from the proof commit.

This assignment concerns Lean and its verification report. Palomar [version 3](palomar/PALOMAR-2026-11-22-000009-v3/README.md) records manuscript v72 at `efda31344ec6420142468ab28af9d96deab571e7`. A new Palomar submission or registration requires a separate author instruction.
