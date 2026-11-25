# WSL2 verification of manuscript v87

Fetch `origin/main`, record the full tested SHA, and verify the [active manifest](../MANUSCRIPT_CURRENT.json) and [correspondence](../FORMALIZATION_STATUS_V87.md) from a clean checkout. The v87 changes to §§4–9 and the bibliography use the existing Lean declarations. All Lean files, the verifier and dependency pins match v86 byte for byte.

1. Check the range computation against `chosenSplitExtension_range`, the PA graph equivalence against `ProvableProgramEquality.precomplete` and `uniform_totalization`, and the binary-name quantifiers against `ComputesReal`, `IsMiller` and `exists_isMiller`. Retain the earlier selector, constant-family and Appendix C checks.
2. Run `python3 scripts/test_verify_axiom_parser.py`, `python3 scripts/verify.py --manuscript-only` and `bash scripts/verify-wsl.sh` on the pinned toolchain. Record all command results, measured inputs and transitive axioms. [Previous full kernel receipt](V84_WSL2_LEAN_VERIFICATION.json.gz)
3. Reconcile the two independent full reports required by [AGENTS.md](../AGENTS.md) on the tested sources. Link the receipt and correspondence from each. The editorial review of §§2–9 and the v84 full verification identify their separate scopes. Use the active edition for this run.
