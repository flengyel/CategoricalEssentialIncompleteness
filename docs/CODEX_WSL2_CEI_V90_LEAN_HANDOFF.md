# WSL2 verification of manuscript v90

Fetch `origin/main` and record the tested commit. The [manifest](../MANUSCRIPT_CURRENT.json) identifies the v90 PDF, sources and [correspondence](../FORMALIZATION_STATUS_V90.md). The Lean tree, verifier and dependency pins match v89.

1. Check Appendix B against the rows for B.1–B.10. For B.7 compare the two endpoint graphs, the center graph and the equality of partial morphisms for every parameter object. Check the application of equation (33) in Proposition 10.1. The [v89 handoff](CODEX_WSL2_CEI_V89_LEAN_HANDOFF.md) lists the preceding Appendix A checks.
2. Run `python3 scripts/test_verify_axiom_parser.py`, `python3 scripts/verify.py --manuscript-only` and `bash scripts/verify-wsl.sh` with the pinned toolchain. Record command results, measured inputs, transitive axioms and the tested commit. [Last full kernel receipt](V84_WSL2_LEAN_VERIFICATION.json.gz)
3. Record and reconcile the two independent full manuscript readings on that revision, with links to the kernel receipt and whole-paper correspondence as specified in [AGENTS.md](../AGENTS.md).
