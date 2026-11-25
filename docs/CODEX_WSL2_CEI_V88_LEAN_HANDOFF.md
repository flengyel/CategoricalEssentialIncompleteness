# WSL2 verification of manuscript v88

Fetch `origin/main`, record the clean source SHA, and use the [current manifest](../MANUSCRIPT_CURRENT.json) and [v88 correspondence](../FORMALIZATION_STATUS_V88.md). The Lean sources, verifier and dependency pins equal v87.

1. For §10 and Appendix B.4, check `ForkTupleTuringChecks.endpoint_graphs`, `endpoint_parameter`, `center_computation` and `fork_parameter` against Proposition 10.1 and (33). Check `ForkCentralNonuniversality.center_not_isTuring` against the central counterexample and `ForkAssociatedTheories` against the direction of the factorization in Corollary 10.9. Retain the checks in the [v87 handoff](CODEX_WSL2_CEI_V87_LEAN_HANDOFF.md).
2. Run `python3 scripts/test_verify_axiom_parser.py`, `python3 scripts/verify.py --manuscript-only` and `bash scripts/verify-wsl.sh` on the pinned toolchain. Record the measured inputs, all command results, the transitive axioms and the tested SHA. [Prior full receipt](V84_WSL2_LEAN_VERIFICATION.json.gz)
3. Reconcile the two full independent reports on the tested revision as specified in [AGENTS.md](../AGENTS.md). Link the receipt and correspondence from each report.
