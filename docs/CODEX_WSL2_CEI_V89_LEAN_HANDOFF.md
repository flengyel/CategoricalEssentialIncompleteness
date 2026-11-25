# WSL2 verification of manuscript v89

Fetch `origin/main`, record its full source SHA, and select the [v89 manifest](../MANUSCRIPT_CURRENT.json) and [correspondence](../FORMALIZATION_STATUS_V89.md) in a clean checkout. The Lean files, verifier and dependency pins match v88.

1. In Appendix A check the deletion identity, the identity and absent-variable substitution equations, and the initial inference algebra. For Lemma A.7 compare both inequalities with `range_regularImage`. Retain the section and appendix checks from the [preceding handoff](CODEX_WSL2_CEI_V88_LEAN_HANDOFF.md).
2. Run `python3 scripts/test_verify_axiom_parser.py`, `python3 scripts/verify.py --manuscript-only` and `bash scripts/verify-wsl.sh` with the pinned toolchain. Record command results, measured inputs, transitive axioms and the tested commit. [Last complete kernel receipt](V84_WSL2_LEAN_VERIFICATION.json.gz)
3. Reconcile the two independent full manuscript readings at the tested revision under [AGENTS.md](../AGENTS.md), with links to the new receipt and the whole-paper correspondence.
